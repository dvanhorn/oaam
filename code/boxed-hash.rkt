#lang racket/base
(require "parameters.rkt" (only-in "nnmapc.rkt" s-map-overlap)
         "data.rkt"
         racket/splicing racket/unsafe/ops)

(struct boxed-hash (hrect map) #:prefab)
(define (bh-boundary bh) (unsafe-struct-ref bh 0))
(define (bh-store bh) (unsafe-struct-ref bh 1))

(define empty-map (boxed-hash #hash() #hash()))

(define (r-new-map) empty-map)

(define (r-map-ref m k [default (λ () (error 'map-ref "Unmapped key ~a" k))])
  (hash-ref (boxed-hash-map m) k default))

(define-syntax-rule (with-boxed-hash . rest-body)
  (begin
    (define (r-map-join-key m k av)
      (match-define (boxed-hash sh h) m)
      (define av* (⊓ (hash-ref h k nothing) av))
      (define int (interval-abstraction av*))
      (boxed-hash (if int (hash-set sh k int) sh) 
                  (hash-set h k av*)))

    (splicing-syntax-parameterize
        ([map-ref (make-rename-transformer #'r-map-ref)]
         [map-join-key (make-rename-transformer #'r-map-join-key)]
         [new-map (make-rename-transformer #'r-new-map)]
         [map-boundary (make-rename-transformer #'bh-boundary)]
         [map-store (make-rename-transformer #'bh-store)])
      . rest-body)))
