#lang racket

(define base-num 10)
(define run-num (make-parameter 5))
(define num-threads 5)

(define (construct-cmd which n file)
  (define path (string->path file))
  (define-values (base filename dir?) (split-path path))
  (define outtime (path-replace-suffix filename (format ".~a.time.~a" which (+ n base-num))))
  (define outmem (path-replace-suffix filename (format ".~a.mem.~a" which (+ n base-num))))
  (format "racket run-benchmark.rkt --~a ~a > bench/~a 2> bench/~a" which file outtime outmem))

(define church "../benchmarks/church.sch")
(define mbrotZ "../benchmarks/mbrotZ.sch")
(define earley "../benchmarks/earley.sch")
(define boyer "../benchmarks/toplas98/boyer.sch")
(define graphs "../benchmarks/toplas98/graphs.sch")
(define lattice "../benchmarks/toplas98/lattice.scm")
(define matrix "../benchmarks/toplas98/matrix.scm")
(define maze "../benchmarks/toplas98/maze.sch") #;call/cc
(define nbody "../benchmarks/toplas98/nbody.sch")
(define nucleic "../benchmarks/toplas98/nucleic.sch")
(define to-test
  (list church mbrotZ earley boyer graphs lattice matrix maze nbody nucleic
   ;;"../benchmarks/toplas98/splay.scm" ;; old match
   ;;"../benchmarks/toplas98/nucleic2.sch" ;; define-syntax
   ;;"../benchmarks/toplas98/handle.scm" ;; old match and defmacro
   ))

(define baseline "bl")
(define specialized "sp")
(define lazy "ls")
(define compiled "lc")
(define deltas "ld")
(define deltasia "ia")
(define deltasid "id")
(define deltaspa "pa")
(define deltaspd "pd")
(define imperative "li")
(define preallocated "lp")

(define which-analyses
  (list deltas
        deltasia
        deltasid
        deltaspa
        deltaspd
        imperative
        preallocated
        baseline 
        specialized
        lazy
        compiled))

(define known-timeout (hash baseline    (set maze graphs matrix nbody)
                            specialized (set maze graphs matrix nbody)
                            lazy        (set maze graphs matrix nbody)
                            compiled    (set maze graphs matrix)                            
                            deltas      (set boyer)
                            ;; All complete
                            imperative  (set)
                            preallocated (set)))
;; 2GB RAM
(define known-exhaust (hash baseline (set nucleic)
                            specialized (set nucleic boyer)
                            lazy (set nucleic boyer)
                            compiled (set nucleic boyer)
                            ;; Must rerun
                            deltas (set)
                            ;; others complete
                            ))

(define (run which file)
  (for* ([n (in-range (run-num))]
         [timeout (in-value (hash-ref known-timeout which (set)))]
         [exhaust (in-value (hash-ref known-timeout which (set)))]
         #:unless (or (set-member? timeout file)
                      (set-member? exhaust file)))
    (printf "Running ~a (count ~a): ~a~%" which n file)
    (system (construct-cmd which n file))))

(define (distribute-threads work)
  (define num (length work))
  (define even (quotient num num-threads))
  (let loop ([w work] [per-thread '()] [thread-num 1])
    (cond [(= thread-num num-threads)
           (cons w per-thread)]
          [else
           (define-values (this rest) (split-at w even))
           (loop rest (cons this per-thread) (add1 thread-num))])))

(define running-threads
  (let ([distributed (distribute-threads
                      (for*/list ([file (in-list to-test)]
                                  [which (reverse which-analyses)])
                        (cons which file)))])
  (for/list ([work-for-thread distributed])
    (thread (λ () (for ([work (in-list work-for-thread)])
                    (run (car work) (cdr work))))))))
(for ([w running-threads]) (thread-wait w))