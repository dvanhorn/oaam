#lang racket

(define run-num 0)

(define (construct-cmd which file)
  (define path (string->path file))
  (define-values (base file dir?) (split-path path))
  (define outfile (path-replace-suffix file (format ".~a.~a" which run-num)))
  (format "~a --~a > ~a" which file outfile))

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
  (list "baseline"
        "0cfa^"
        "lazy-0cfa^"
        "lazy-0cfa^/c"
        "lazy-0cfa∆s/c"
        "lazy-0cfa^/c!"
        "lazy-0cfa^/c/prealloc!"))

(for* ([which which-analyses]
       [file to-test])
  (system (construct-cmd which file)))