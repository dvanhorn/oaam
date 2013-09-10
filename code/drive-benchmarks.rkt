#lang racket

;; This module drives [run-benchmark.rkt] with several algorithms/benchmarks 
;; to run in parallel. Since we want the output of each run of each algorithm/benchmark,
;; we label the run numbers in the interval [base-num, base-num + run-num).

;; The parallelism is determined by num-threads. There is no work-stealing,
;; so some threads will finish far sooner than others. This has not been a problem,
;; and we could do better with minimal effort by randomly shuffling the worklist
;; before distributing it to the threads (see the main submodule below).

;; NOTE: if base-num or run-num change, you must manually change [code/bench/out.sh]
;; and [paper/proctime.rkt] to be consistent with the number range.
(define base-num 0)
(define run-num 5)
(define num-threads 1)

;; In order to get consistent benchmarking numbers, each run is in a /fresh/
;; Racket VM, which we spin up with a shell command. The analysis statistics are
;; printed to stdout, and the memory statistics to stderr.
;; 
;; See [code/bench/out.sh] for the script we used to distill the output info
;; that is processed by [paper/proctime.rkt]
(define (construct-cmd which n file)
  (define path (string->path file))
  (define-values (base filename dir?) (split-path path))
  (define outtime (path-replace-suffix filename (format ".~a.time.~a" which (+ n base-num))))
  (define outmem (path-replace-suffix filename (format ".~a.mem.~a" which (+ n base-num))))
  (format "racket run-benchmark.rkt --~a ~a > bench/~a 2> bench/~a" which file outtime outmem))

;; We identify benchmarks so that we can collect stats easier in [proctime.rkt] (LOC, etc.)
(define sort1 "../benchmarks/temp-c/sort.sch")
(define sort2 "../benchmarks/temp-c/sort-pushdown.sch")
(define sort3 "../benchmarks/temp-c/sort-lists.sch")
(define file "../benchmarks/temp-c/file.sch")
(define to-test
  (list #;#;sort1 sort2 sort3 file
   ))

(module+ data (provide sort1 sort2 sort3 file to-test))

;; Algorithm tags used to drive [run-benchmark.rkt]
(define baseline "ps")
(define μ "psu")
(define Ξ "psp")
(define Γ "lcg")
(define Γτ "lcgt")
(define μΓτ "lcgut")
(define μΓτΞ "lcgutp")

(define which-analyses
  (list baseline μ Ξ Γ Γτ μΓτ μΓτΞ
        ))

(define (run which file)
  (for ([n (in-range run-num)])
    (printf "Running ~a (count ~a): ~a~%" which n file)
    (system (construct-cmd which n file))))

;; Split work "evenly" by number of threads.
;; The last thread gets the remainder of integer division in addition to
;; its "even" allotment.
(define (distribute-threads work)
  (define num (length work))
  (define even (quotient num num-threads))
  (let loop ([w work] [per-thread '()] [thread-num 1])
    (cond [(= thread-num num-threads)
           (cons w per-thread)]
          [else
           (define-values (this rest) (split-at w even))
           (loop rest (cons this per-thread) (add1 thread-num))])))

(module+ main
  ;; Spin up threads
  (define running-threads
    (let ([distributed (distribute-threads
                        (for*/list ([file (in-list to-test)]
                                    [which (reverse which-analyses)])
                          (cons which file)))])
      (for/list ([work-for-thread distributed])
        (thread (λ () (for ([work (in-list work-for-thread)])
                        (run (car work) (cdr work))))))))
  ;; Join all threads
  (for ([w running-threads]) (thread-wait w)))
