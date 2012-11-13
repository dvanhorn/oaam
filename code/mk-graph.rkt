#lang racket
(require "kcfa-instantiations.rkt" "run-benchmark.rkt" "graph.rkt")

(define benchmark "../benchmarks/church.sch")
(define prefix
  (let-values ([(base filename dir?) (split-path (string->path benchmark))])
    filename))

(define (do eval suffix)
  (define pdf (path-replace-suffix prefix (format "~a.dot" suffix)))
  (parameterize ([graph-file (path-replace-suffix prefix (format "~a.dot" suffix))]
                 [aval eval])
    (test (prep benchmark))
    (system (format "dot -Tpdf -o ~a ~a" (graph-file) pdf))))

(do 0cfa^ "-base")
(do lazy-0cfa^ "-lazy")
(do lazy-0cfa^/c "-lazyc")

