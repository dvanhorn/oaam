#lang racket
(provide extend* join-store
         update would-update? restrict-to-set
         mk-restrict-to-reachable
         restrict-to-reachable
         restrict-to-reachable/vector)
(require "data.rkt" "ast.rkt" "notation.rkt" racket/splicing racket/stxparam)

(define (extend* ρ xs vs)
  (for/fold ([ρ ρ]) ([x (in-list xs)] [v (in-list vs)])
    (hash-set ρ x v)))
(define-syntax-rule (join eσ a s)
  (hash-set eσ a (⊓ s (hash-ref eσ a nothing))))

;; Perform join and return if the join was idempotent
(define-syntax-rule (join/change eσ a s)
  (let ()
    (define prev (hash-ref eσ a nothing))
    (define s* (⊓ s prev))
    (values (hash-set eσ a s*) (≡ prev s*))))

(define-syntax-rule (no-change? eσ a s)
  (⊑? s (hash-ref eσ a nothing)))

;; Store Store -> Store
(define-syntax-rule (join-store eσ1 eσ2)
  (for/fold ([eσ eσ1])
      ([(k v) (in-hash eσ2)])
    (join eσ k v)))

(define-syntax-rule (update ∆s eσ)
  (for/fold ([eσ eσ]) ([a×vs (in-list ∆s)])
    (join eσ (car a×vs) (cdr a×vs))))

(define-syntax-rule (would-update? ∆s eσ)
  (not (for/and ([a×vs (in-list ∆s)]) (no-change? eσ (car a×vs) (cdr a×vs)))))

(define (restrict-to-set map s)
  (for/hash ([a (in-set s)])
    (values a (hash-ref map a))))

(define-syntax-rule (mk-reach ref touches)
  (λ (eσ root)
     (define seen ∅)
     (let loop ([as root])
       (for/union #:res acc ([a (in-set as)]
                             #:unless (a . ∈ . seen))
                  (set! seen (∪1 seen a))
                  (for/union #:initial (∪1 acc a)
                             ([v (in-abstract-values (ref eσ a))])
                    (loop (touches v)))))))

(define-simple-macro* (mk-restrict-to-reachable name ref touches)
  (define name
    (let ([reach (mk-reach ref touches)])
      (λ (eσ v)
         (for/hash ([a (in-set (reach eσ (touches v)))])
           (values a (ref eσ a)))))))

(define-syntax-parameter restrict-to-reachable #f)
(define-syntax-parameter restrict-to-reachable/vector #f)