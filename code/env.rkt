#lang racket
(provide extend extend* join join* join-store
         update update/change restrict-to-reachable restrict-to-reachable/vector)
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

;; Store Store -> Store
(define (join-store eσ1 eσ2)
  (for/fold ([eσ eσ1])
      ([(k v) (in-hash eσ2)])
    (join eσ k v)))

(define (update ∆s eσ)
  (for/fold ([eσ eσ]) ([a×vs (in-list ∆s)])
    (join eσ (car a×vs) (cdr a×vs))))
;; Like update, only returns if the update was idempotent
(define (update/change ∆s eσ)
  (for/fold ([eσ eσ] [same? #t]) ([a×vs (in-list ∆s)])
    (define-values (σ* a-same?) (join/change eσ (car a×vs) (cdr a×vs)))
    (values σ* (and same? a-same?))))

(define (((mk-reach ref) touches) eσ root)
  (define seen ∅)
  (let loop ([as root])
    (for/union #:res acc ([a (in-set as)]
                          #:unless (a . ∈ . seen))
               (set! seen (∪1 seen a))
               (for/union #:initial (∪1 acc a)
                          ([v (in-set (ref eσ a))])
                          (loop (touches v))))))

(define ((mk-restrict-to-reachable ref) touches)
  (define reach ((mk-reach ref) touches))
  (λ (eσ v)
     (for/hash ([a (in-set (reach eσ (touches v)))])
       (values a (ref eσ a)))))

(define reach (mk-reach hash-ref))
(define reach/vec (mk-reach vector-ref))

(define restrict-to-reachable (mk-restrict-to-reachable hash-ref))
(define restrict-to-reachable/vector (mk-restrict-to-reachable vector-ref))
