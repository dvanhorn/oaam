#lang racket

(define run-num 0)

(define (construct-cmd which file)
  (define path (string->path file))
  (define-values (base filename dir?) (split-path path))
  (define outtime (path-replace-suffix filename (format ".~a.time.~a" which run-num)))
  (define outmem (path-replace-suffix filename (format ".~a.mem.~a" which run-num)))
  (format "racket run-benchmark.rkt --~a ~a > ~a 2> ~a" which file outtime outmem))

(define to-test
  (list "../benchmarks/church.sch"
        "../benchmarks/mbrotZ.sch"
        "../benchmarks/earley.sch"
        "../benchmarks/toplas98/boyer.sch"
        "../benchmarks/toplas98/graphs.sch"
        "../benchmarks/toplas98/lattice.scm"
        "../benchmarks/toplas98/matrix.scm"
        "../benchmarks/toplas98/maze.sch" ;; call/cc
        "../benchmarks/toplas98/nbody.sch"
        "../benchmarks/toplas98/nucleic.sch"
        ;;"../benchmarks/toplas98/splay.scm" ;; old match
        ;;"../benchmarks/toplas98/nucleic2.sch" ;; define-syntax
        ;;"../benchmarks/toplas98/handle.scm" ;; old match and defmacro
))

(define which-analyses
  (list  "bl"
         "sp"
         "ls"
         "lc"
         "ld"
         "li"
         "lp"))

(for* ([which which-analyses]
       [file to-test])
  (printf "Running ~a: ~a~%" which file)
  (system (construct-cmd which file)))