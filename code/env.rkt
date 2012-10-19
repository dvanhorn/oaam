#lang racket
(provide (all-defined-out))
(require "data.rkt" "ast.rkt" "notation.rkt")

(define (extend ρ x v)
  (hash-set ρ x v))
(define (extend* ρ xs vs)
  (cond [(empty? xs) ρ]
        [else (extend* (extend ρ (first xs) (first vs))
                       (rest xs)
                       (rest vs))]))
(define (join σ a s)
  (hash-set σ a
            (∪ s (hash-ref σ a ∅))))
(define (join* σ as ss)
  (cond [(empty? as) σ]
        [else (join* (join σ (first as) (first ss))
                     (rest as)
                     (rest ss))]))
(define (join-one σ a x)
  (hash-set σ a (∪1 (hash-ref σ a ∅) x)))
(define (join-one* σ as xs)
  (cond [(empty? as) σ]
        [else (join-one* (join-one σ (first as) (first xs))
                         (rest as)
                         (rest xs))]))

;; Store Store -> Store
(define (join-store σ1 σ2)
  (for/fold ([σ σ1])
    ([k×v (in-hash-pairs σ2)])
    (hash-set σ (car k×v)
              (∪ (cdr k×v)
                         (hash-ref σ (car k×v) ∅)))))

(define (update ∆s σ)
  (for/fold ([σ σ]) ([a×vs (in-list ∆s)])
    (join σ (car a×vs) (cdr a×vs))))
#;
;; Set State -> Store
(define (join-stores ss)
  (for/fold ([σ (hash)])
    ([s ss])
    (join-store σ (state-σ s))))

(define ((mk-reach ref 0cfa?) σ root)
  (define seen ∅)
  (let loop ([as root])
    (for/union #:res acc ([a (in-set as)]
                          #:unless (a . ∈ . seen))
               (set! seen (∪1 seen a))
               (for/union #:initial (∪1 acc a)
                          ([v (in-set (ref σ a))])
                          (loop (touches v 0cfa?))))))

(define (mk-restrict-to-reachable ref 0cfa?)
  (define reach (mk-reach ref (if 0cfa? reach-0 reach-k)))
  (λ (σ v)
     (for/hash ([a (in-set (reach σ (touches v 0cfa?)))])
       (values a (hash-ref σ a)))))

(define reach-0 (mk-reach hash-ref #t))
(define reach-k (mk-reach hash-ref #f))
(define reach/vec-0 (mk-reach vector-ref #t))
(define reach/vec-k (mk-reach vector-ref #f))


(define restrict-to-reachable-0 (mk-restrict-to-reachable hash-ref #t))
(define restrict-to-reachable-k (mk-restrict-to-reachable hash-ref #f))
(define restrict-to-reachable/vector-0 (mk-restrict-to-reachable vector-ref #t))
(define restrict-to-reachable/vector-k (mk-restrict-to-reachable vector-ref #f))
