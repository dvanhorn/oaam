#lang racket
(require "do.rkt" "data.rkt" "primitives.rkt" "parameters.rkt" racket/splicing)
(provide with-lazy with-strict)

(define-syntax-rule (bind-delay-lazy (res ldσ a) body)
  (let ([res (singleton (addr a))]) body))
(define-syntax-rule (bind-delay-strict (res ldσ a) body)
  (bind-get (res ldσ a) body))

(define-syntax-rule (bind-force-lazy (res σ v) body)
  (match v
    [(addr a) (bind-get (res σ a) body)]
    [(value-set vs) (let ([res vs]) body)]
    [other (let ([res (singleton other)]) body)]))

(define-syntax-rule (bind-force-strict (res σ v) body)
  (let ([res (singleton v)]) body))

(define-syntax-rule (with-lazy body)
  (splicing-syntax-parameterize
   ([bind-delay (make-rename-transformer #'bind-delay-lazy)]
    [bind-force (make-rename-transformer #'bind-force-lazy)])
   body))

(define-syntax-rule (with-strict body)
  (splicing-syntax-parameterize
   ([bind-delay (make-rename-transformer #'bind-delay-strict)]
    [bind-force (make-rename-transformer #'bind-force-strict)])
   body))

