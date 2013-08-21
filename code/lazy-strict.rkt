#lang racket
(require "data.rkt" "primitives.rkt" racket/splicing)
(provide with-lazy with-strict)

(define-syntax-rule (lazy-force x)
  (match x
    [(addr a) (getter a)]
    [(? set-immutable?) x]
    [v (singleton v)]))
(define-syntax-rule (strict-force x) (let ([v x]) (if (set-immutable? v) v (singleton v))))

(define-syntax-rule (lazy-delay a) (singleton (addr a)))
(define-syntax-rule (strict-delay a) (getter a))

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

