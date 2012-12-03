#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "fix.rkt" "handle-limits.rkt"
         "graph.rkt")
(provide with-cfa2^)

(define-syntax-rule (with-cfa2^ (mk-analysis) body)
  (syntax-parameterize ([in-scope-of-extras (mk-cfa2 #'co #'ap)])
    (let-syntax ([mk-analysis
                  (syntax-rules ()
                    [(_ . args) (mk-analysis #:extra (ξ)
                                             #:
                                             . args)])]))))