#lang racket

(provide (all-defined-out))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common environment metafunctions for functional representations
(define (join-store σ1 σ2)
  (for/fold ([σ σ1])
    ([k×v (in-hash-pairs σ2)])
    (hash-set σ (car k×v)
              (set-union (cdr k×v)
                         (hash-ref σ (car k×v) (set))))))

;; Set State -> Store
(define (join-stores ss)
  (for/fold ([σ (hash)])
    ([s ss])
    (join-store σ (car s))))

(define (join-one σ a x)
  (hash-set σ a
            (set-add (hash-ref σ a (set)) x)))
(define (join-one* σ as xs)
  (cond [(empty? as) σ]
        [else (join-one* (join-one σ (first as) (first xs))
                         (rest as)
                         (rest xs))]))
(define (join σ a s)
  (hash-set σ a
            (set-union s (hash-ref σ a (set)))))

(define (get-cont σ l)
  (hash-ref σ l (λ () (error 'get-cont "Unbound cont ~a" l))))

(define (extend ρ x v)
  (hash-set ρ x v))

(define (lookup-store σ a)
  (hash-ref σ a (λ () (error 'lookup-store "Unbound address ~a" a))))