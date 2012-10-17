#lang racket
(provide (all-defined-out))
(require "data.rkt" "ast.rkt" "notation.rkt")

(define (lookup ρ σ x)
  (hash-ref σ (hash-ref ρ x)))
(define (lookup-env ρ x)
  (hash-ref ρ x))
(define (lookup-sto σ x)
  (hash-ref σ x))
(define (get-cont σ l)
  (hash-ref σ l))
(define (extend ρ x v)
  (hash-set ρ x v))
(define (extend* ρ xs vs)
  (cond [(empty? xs) ρ]
        [else (extend* (extend ρ (first xs) (first vs))
                       (rest xs)
                       (rest vs))]))
(define (join σ a s)
  (hash-set σ a
            (set-union s (hash-ref σ a (set)))))
(define (join* σ as ss)
  (cond [(empty? as) σ]
        [else (join* (join σ (first as) (first ss))
                     (rest as)
                     (rest ss))]))
(define (join-one σ a x)
  (hash-set σ a
            (set-add (hash-ref σ a (set)) x)))
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
              (set-union (cdr k×v)
                         (hash-ref σ (car k×v) (set))))))

(define (update ∆s σ)
  (for/fold ([σ σ]) ([a×vs (in-list ∆s)])
    (join σ (car a×vs) (cdr a×vs))))
#;
;; Set State -> Store
(define (join-stores ss)
  (for/fold ([σ (hash)])
    ([s ss])
    (join-store σ (state-σ s))))

(define ((mk-reach ref) σ root)
  (define seen ∅)
  (let loop ([as root])
    (for/union #:res acc ([a (in-set as)]
                          #:unless (a . ∈ . seen))
               (set! seen (∪1 seen a))
               (for/union #:initial (∪1 acc a)
                          ([v (in-set (ref σ a))])
                          (loop (touches v))))))

(define reach (mk-reach hash-ref))
(define reach/vec (mk-reach vector-ref))

(define (restrict-to-reachable σ v)
  (for/hash ([a (in-set (reach σ (touches v)))])
    (values a (hash-ref σ a))))
;; not really a restriction since it's not a vector, but meh.
(define (restrict-to-reachable/vector σvec v)
  (for/hash ([a (in-set (reach/vec σvec
                                   (if (set? v)
                                       (for/union ([v* (in-set v)]) (touches v*))
                                       (touches v))))])
    (values a (vector-ref σvec a))))