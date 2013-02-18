#lang racket/base
(require "notation.rkt" "parameters.rkt"
         (for-syntax racket/base)
         "data.rkt" racket/splicing)
(provide with-simple-heap s-map-overlap s-map-distance)

(define (s-map-ref m k [default (λ () (error 'map-ref "Unmapped ~a" k))])
  (hash-ref m k default))
#;(define (map-remove m k v) (error 'TODO))

(define (s-map-overlap m₀ m₁) 
  (for*/set ([(a v) (in-hash m₀)]
             [v* (in-value (hash-ref m₁ a #f))]
             #:when (equal? v v*))
    a))

;; INVARIANT: maps never contain #f
(define (s-map-distance m₀ m₁)
  (define in-1-but-not-0
    (for/sum ([a (in-hash-keys m₁)] #:unless (hash-has-key? m₀ a)) 1))
  (for/fold ([out in-1-but-not-0]) ([(a v) (in-hash m₀)])
    (if (and #:bind r (hash-ref m₁ a #f)
             (equal? r v))
        out
        (add1 out))))

(define-syntax-rule (with-simple-heap . rest-body)
  (begin
    (define (s-map-join-key m k av)
      (hash-set m k (⊓ (hash-ref m k nothing) av)))

    (splicing-syntax-parameterize
        ([map-ref (make-rename-transformer #'s-map-ref)]
         [map-join-key (make-rename-transformer #'s-map-join-key)]
         [new-map (make-rename-transformer #'hash)]
         [map-distance (make-rename-transformer #'s-map-distance)]
         [map-overlap (make-rename-transformer #'s-map-overlap)])
      . rest-body)))