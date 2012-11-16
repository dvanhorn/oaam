#lang racket
(require "do.rkt" "data.rkt" "primitives.rkt" racket/splicing)
(provide with-lazy with-strict)

(define-syntax-rule (lazy-force lfσ x)
  (match x
    [(addr a) (getter lfσ a)]
    [v (singleton v)]))
(define-syntax-rule (strict-force lfσ x) (singleton x))

(define-syntax-rule (lazy-delay ldσ a) (singleton (addr a)))
(define-syntax-rule (strict-delay ldσ a) (getter ldσ a))

(define-syntax-rule (bind-delay-lazy (res ldσ a) body)
  (let ([res (singleton (addr a))]) body))
(define-syntax-rule (bind-delay-strict (res ldσ a) body)
  (bind-get (res ldσ a) body))

(define-syntax-rule (bind-force-lazy (res σ v) body)
  (match v
    [(addr a) (bind-get (res σ a) body)]
    [other (let ([res (singleton other)]) body)]))

(define-syntax-rule (bind-force-strict (res σ v) body)
  (let ([res (singleton v)]) body))

(define-syntax-rule (with-lazy body)
  (splicing-syntax-parameterize
   ([delay (make-rename-transformer #'lazy-delay)]
    [force (make-rename-transformer #'lazy-force)]
    [bind-delay (make-rename-transformer #'bind-delay-lazy)]
    [bind-force (make-rename-transformer #'bind-force-lazy)])
   body))

(define-syntax-rule (with-strict body)
  (splicing-syntax-parameterize
   ([delay (make-rename-transformer #'strict-delay)]
    [force (make-rename-transformer #'strict-force)]
    [bind-delay (make-rename-transformer #'bind-delay-strict)]
    [bind-force (make-rename-transformer #'bind-force-strict)])
   body))

