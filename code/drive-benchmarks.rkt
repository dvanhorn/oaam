#lang racket

(define run-num 0)

(define (construct-cmd which file)
  (define path (string->path file))
  (define-values (base filename dir?) (split-path path))
  (define outtime (path-replace-suffix filename (format ".~a.time.~a" which run-num)))
  (define outmem (path-replace-suffix filename (format ".~a.mem.~a" which run-num)))
  (format "racket run-benchmark.rkt --~a ~a > ~a 2> bench/~a" which file outtime outmem))

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
(define imperative "li")
(define preallocated "lp")

(define which-analyses
  (list baseline 
        specialized
        lazy
        compiled
        deltas
        imperative
        preallocated))

(define known-timeout (hash baseline    (set boyer graphs matrix nbody)
                            specialized (set boyer graphs matrix nbody)
                            lazy        (set boyer graphs matrix nbody)
                            compiled    (set boyer graphs matrix)
                            deltas      (set church mbrotZ)))
;; 2GB RAM
(define known-exhaust (hash baseline (set nucleic)
                            specialized (set nucleic)
                            lazy (set nucleic)
                            compiled (set nucleic)))

(for* ([which which-analyses]
       [timeout (in-value (hash-ref known-timeout which (set)))]
       [exhaust (in-value (hash-ref known-timeout which (set)))]
       [file to-test]
       #:unless (or (set-member? timeout file)
                    (set-member? exhaust file)))
  (printf "Running ~a: ~a~%" which file)
  (system (construct-cmd which file)))