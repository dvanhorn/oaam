#lang racket/base
(require "notation.rkt" (except-in racket/set for/set for*/set) racket/contract)
;; nnmapc - Nearest-neighbors map collection

(provide new-map map-set
         map-ref map-map-close
         new-map-map map-map-set map-map-ref
         map-map-iterate-first
         map-map-iterate-key
         map-map-iterate-value
         map-map-iterate-next)

;; This module defines and naively implements an interface for a
;; collection of finite maps that form a metric space with the
;; ability to compute a (approximate if need be) nearest-neighbors set.

;; The reality is that there will be several collections created of
;; the carrier maps, and we want to have relatively low cost nearest-neighbors
;; within collections. By coordinating the entire space, we hope to manage
;; some of the computational cost associated with calculating nearest neighbors.

;; The purpose is to allow the represetations of stores have a notion
;; of distance from other stores. This interface will facilitate a better
;; implementation of congruence for the narrow sparse analysis algorithm.

;; Two stores are congruent on a set of addresses when they have the same
;; entries for each address. With more care, we can relax this into a non-symmetric
;; relation where the entries of one are less (in the value lattice) than the other.
;; This relaxation is not yet a consideration in the nearest neighbors computation.

;; Representations of equivalent maps need to be equal in order for the fixpoint to work.
;; That is, if a state has been seen, we use an equal? hash to check.
;; Not equal -> possible non-termination

(define (new-map) (hash))
(define (map-set m k v) (hash-set m k v))
(define (map-ref m k [default (λ () (error 'map-ref "Unmapped ~a" k))])
  (hash-ref m k default))
#;(define (map-remove m k v) (error 'TODO))

;; Instead of a collection of maps, we actually map collections to values,
;; so we use a map rather than use a collection interface.

;; We use a locality-sensitive hashing scheme for the above maps, which uses this metric:
;; d(σ₀, σ₁) = |{a :: σ₀^⊥(a) ≠ σ₁^⊥(a)}|
;; Informally, this is the amount of changes needed to transform a map to the other.
;; This forms a true metric (self-0, symmetric and triangle-ineq)

(define (new-map-map) (hash))
(define (map-map-set mm m v) (hash-set mm m v))
(define map-map-ref hash-ref)
#;(define (map-map-remove mm m) (error 'TODO))

(define (map-map-iterate-first mm) (hash-iterate-first mm))
(define (map-map-iterate-key mm itr) (hash-iterate-key mm itr))
(define (map-map-iterate-value mm itr) (hash-iterate-value mm itr))
(define (map-map-iterate-next mm itr) (hash-iterate-next mm itr))

;; INVARIANT: maps never contain #f
(define (map-distance m₀ m₁)
  (define in-1-but-not-0
    (for/sum ([a (in-hash-keys m₁)] #:unless (hash-has-key? m₀ a)) 1))
  (for/fold ([out in-1-but-not-0]) ([(a v) (in-hash m₀)])
    (if (and #:bind r (hash-ref m₁ a #f)
             (equal? r v))
        out
        (add1 out))))

(define (map-overlap m₀ m₁) 
  (unless (and (hash? m₀) (hash? m₁))
    (error 'map-overlap "Bad map-map ~a ~a" m₀ m₁))
  (for*/set ([(a v) (in-hash m₀)]
             [v* (in-value (hash-ref m₁ a #f))]
             #:when (equal? v v*))
    a))

;; Map-Map[A] Map -> (values Map Set[Key])
;; Find a map in the given collection that is "reasonably close" to
;; the given map, and which key Also return the set of keys on which both maps overlap.
(define (map-map-close mm m)
  (define-values (min-map min-dist max-overlap)
    (for/fold ([min-map #f] [mind #f] [maxo #f])
        ([(key val) (in-hash mm)])
      (define dist (map-distance key m))
      (cond [(or (not mind) (< dist mind))
             (values key dist (map-overlap key m))]
            [(= dist mind)
             (define ovr (map-overlap key m))
             (if (< (set-count maxo) (set-count ovr))
                 (values key dist ovr)
                 (values min-map mind maxo))]
            [else (values min-map mind maxo)])))
  (values min-map max-overlap))
