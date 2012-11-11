#lang racket
(require "data.rkt" "primitives.rkt" racket/splicing)
(provide with-lazy with-strict)

(define-syntax-rule (lazy-force lfσ x)
  (match x
    [(addr a) (getter lfσ a)]
    [v (singleton v)]))
(define-syntax-rule (strict-force lfσ x) (singleton x))

(define-syntax-rule (lazy-delay ldσ a) (singleton (addr a)))
(define-syntax-rule (strict-delay ldσ a) (getter ldσ a))

(define-syntax-rule (with-lazy body)
  (splicing-syntax-parameterize
   ([delay (make-rename-transformer #'lazy-delay)]
    [force (make-rename-transformer #'lazy-force)])
   body))

(define-syntax-rule (with-strict body)
  (splicing-syntax-parameterize
   ([delay (make-rename-transformer #'strict-delay)]
    [force (make-rename-transformer #'strict-force)])
   body))

