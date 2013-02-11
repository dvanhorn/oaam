#lang racket/base
(require "notation.rkt"
         racket/stxparam racket/splicing
         (for-syntax racket/base)
         (except-in racket/set for/set for*/set) racket/contract)
;; nnmapc - Nearest-neighbors map collection

(provide new-map map-set
         map-ref map-map-close
         new-map-map map-map-add! map-map-ref
         in-map-map-values
         ;; for use in rtee-nnmapc
         map-overlap
         with-simple-nnmapc)
(define-syntax-rule (define-syntax-parameters p ...)
  (begin (define-syntax-parameter p #f) ...))
(define-syntax-parameters new-map map-set map-ref map-map-close
  new-map-map map-map-add! map-map-ref in-map-map-values)
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

(define (s-map-ref m k [default (λ () (error 'map-ref "Unmapped ~a" k))])
  (hash-ref m k default))
#;(define (map-remove m k v) (error 'TODO))

;; Instead of a collection of maps, we actually map collections to values,
;; so we use a map rather than use a collection interface.

;; We use a locality-sensitive hashing scheme for the above maps, which uses this metric:
;; d(σ₀, σ₁) = |{a :: σ₀^⊥(a) ≠ σ₁^⊥(a)}|
;; Informally, this is the amount of changes needed to transform a map to the other.
;; This forms a true metric (self-0, symmetric and triangle-ineq)

(define (s-map-map-add! mm m v)
  (define m-hash (hash-ref! mm m make-hasheq))
  (hash-set! m-hash v #t)
  mm)

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
  (for*/set ([(a v) (in-hash m₀)]
             [v* (in-value (hash-ref m₁ a #f))]
             #:when (equal? v v*))
    a))

;; Map-Map[A] Map -> (values Map Set[Key])
;; Find a map in the given collection that is "reasonably close" to
;; the given map, and which key Also return the set of keys on which both maps overlap.
(define (s-map-map-close mm m accept)
  (unless (hash? mm) (error 'map-map-close "Bad ~a" mm))
  (define-values (min-map min-value min-dist max-overlap)
    (for/fold ([min-map #f] [minv #f] [mind #f] [maxo #f])
        ([(key val) (in-hash mm)])
      (define dist (map-distance key m))
      (cond [(or (not mind) (< dist mind))
             (values key val dist (map-overlap key m))]
            [(= dist mind)
             (define ovr (map-overlap key m))
             (if (< (set-count maxo) (set-count ovr))
                 (values key val dist ovr)
                 (values min-map minv mind maxo))]
            [else (values min-map minv mind maxo)])))
  (define-values (out0 out1) (accept min-map max-overlap min-value))
  (if out0
      (values min-map max-overlap out0 out1)
      (values #f #f #f #f)))

(define-syntax-rule (with-simple-nnmapc . rest-body)
  (splicing-syntax-parameterize
      ([map-ref (make-rename-transformer #'s-map-ref)]
       [map-set (make-rename-transformer #'hash-set)]
       [new-map (make-rename-transformer #'hash)]
       [new-map-map (make-rename-transformer #'make-hash)]
       [map-map-ref (make-rename-transformer #'hash-ref)]
       [map-map-close (make-rename-transformer #'s-map-map-close)]
       [map-map-add! (make-rename-transformer #'s-map-map-add!)]
       [in-map-map-values (make-rename-transformer #'in-set)])
    . rest-body))