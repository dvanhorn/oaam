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
(define num-threads 2)

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
(define church "../benchmarks/church.sch")
(define mbrotZ "../benchmarks/mbrotZ.sch")
(define earley "../benchmarks/earley.sch")
(define boyer "../benchmarks/toplas98/boyer.sch")
(define graphs "../benchmarks/toplas98/graphs.sch")
(define lattice "../benchmarks/toplas98/lattice.scm")
(define matrix "../benchmarks/toplas98/matrix.scm")
(define maze "../benchmarks/toplas98/maze.sch")
(define nbody "../benchmarks/toplas98/nbody.sch")
(define nucleic "../benchmarks/toplas98/nucleic.sch")
(define to-test
  (list church mbrotZ earley lattice graphs boyer matrix maze nbody nucleic))

(module+ data (provide church mbrotZ earley boyer graphs lattice matrix maze nbody nucleic to-test))

;; Algorithm tags used to drive [run-benchmark.rkt]
(define baseline "sp")
(define lazy "ls")
(define compiled "lc")
(define deltas "ld")
(define deltasid "id")
(define deltasis "is")
(define deltaspd "pd")
(define deltasps "ps")
;; Not in paper since insignificant or worse performance+precision
(define deltasfd "fd")
(define imperative "it")
(define preallocated "pt")
(define deltasia "ia")
(define deltaspa "pa")

(define which-analyses
  (list
   ;; deltasfd ;; like deltaspd, only purely functional. Unfortunately slow.
   baseline
   lazy
   compiled
   deltas
;; imperative   ;; timestamp approximation, not in paper.
;; preallocated ;; timestamp approximation, not in paper.
#|
   deltasid
   deltaspd
|#
   deltasis
   deltasps))

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
