#lang racket
(provide extend extend* join join* join-store join-store/change
         restrict-to-set reach
         update update/change would-update? restrict-to-reachable restrict-to-reachable/vector)
(require "data.rkt" "ast.rkt" "notation.rkt")

(define (extend ρ x v)
  (hash-set ρ x v))
(define (extend* ρ xs vs)
  (for/fold ([ρ ρ]) ([x (in-list xs)] [v (in-list vs)])
    (hash-set ρ x v)))
(define (join eσ a s)
  (hash-set eσ a (⊓ s (hash-ref eσ a ∅))))
(define (join* eσ as ss)
  (for/fold ([eσ eσ]) ([a as] [s ss]) (join eσ a s)))

;; Perform join and return if the join was idempotent
(define (join/change eσ a s)
  (define prev (hash-ref eσ a ∅))
  (define s* (⊓ s prev))
  (values (hash-set eσ a s*) (≡ prev s*)))

(define (no-change? eσ a s)
  (⊑? s (hash-ref eσ a nothing)))

;; Store Store -> Store
(define (join-store eσ1 eσ2)
  (for/fold ([eσ eσ1])
      ([(k v) (in-hash eσ2)])
    (join eσ k v)))

(define (join-store/change eσ1 eσ2)
  (for/fold ([eσ eσ1] [same? #t])
      ([(k v) (in-hash eσ2)])
    (define-values (eσ* same?*) (join/change eσ k v))
    (values eσ* (and same? same?*))))

(define (update ∆s eσ)
  (for/fold ([eσ eσ]) ([a×vs (in-list ∆s)])
    (join eσ (car a×vs) (cdr a×vs))))

(define (update/change ∆s eσ)
  (for/fold ([eσ eσ] [same? #t]) ([a×vs (in-list ∆s)])
    (define-values (σ* a-same?) (join/change eσ (car a×vs) (cdr a×vs)))
    (values σ* (and same? a-same?))))

(define (would-update? ∆s eσ)
  (not (for/and ([a×vs (in-list ∆s)]) (no-change? eσ (car a×vs) (cdr a×vs)))))

(define (((mk-reach ref) touches) eσ root)
  (define seen (make-hasheq))
  (let loop ([as root])
    (for/union #:res acc ([a (in-set as)]
                          #:unless (hash-has-key? seen a))
               (hash-set! seen a #t)
               (for/union #:initial (∪1 acc a)
                          ([v (in-set (ref eσ a ∅))])
                          (loop (touches v))))))

(define (restrict-to-set ρ S)
  (for/hash ([(x a) (in-hash ρ)]
             #:when (x . ∈ . S))
    (values x a)))
(define ((mk-restrict-to-reachable ref) touches)
  (define reach ((mk-reach ref) touches))
  (λ (eσ v)
     (for/hash ([a (in-set (reach eσ (touches v)))])
       (values a (ref eσ a)))))

(define reach (mk-reach hash-ref))
(define reach/vec (mk-reach vector-ref))

(define restrict-to-reachable (mk-restrict-to-reachable hash-ref))
(define restrict-to-reachable/vector (mk-restrict-to-reachable vector-ref))
