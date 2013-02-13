#lang racket
(require racket/unsafe/ops
         "nnmapc.rkt")
(provide with-spectral-heap)
;; Addresses in abstract interpretation change with varying frequency.
;; Comparing two heaps can be expensive, so if we can partition out slow-change
;; from fast-change, we can be reasonably sure that slowly changing heaps
;; will compare positively more often. Indeed they could have pointer equality
;; with much higher probability. We expect most addresses to be slow-changing.

;; Fast-changing addresses we expect to be less abundant, and thus the fast-changing
;; heaps would be smaller and more amenable to computational scrutiny.
;; The lower dimensionality of the heap could also help with spatial indexing to
;; find heaps that are few changes different from a given one.

;; A spectral heap is split along a given spectrum of variability of each region.
;; Variability is tract by the statistics of the heap

(define/match (spectral-equal? s0 s1 r-equal?)
  [((spectral s0 m0 f0 _) (spectral s1 m1 f1 _) _)
   (and (r-equal? s0 s1)
        (r-equal? m0 m1)
        (r-equal? f0 f1))])

(define/match (spectral-hash s r-equal-hash-code)
  [((spectral s m f _) _)
   (unsafe-fxxor
    (unsafe-fxxor (r-equal-hash-code s)
                  (r-equal-hash-code m))
    (r-equal-hash-code f))])

(define/match (spectral-hash2 s r-equal-secondary-hash-code)
  [((spectral s m f _) _)
   (unsafe-fxxor
    (unsafe-fxxor (r-equal-secondary-hash-code s)
                  (r-equal-secondary-hash-code m))
    (r-equal-secondary-hash-code f))])

(struct spectral (slow medium fast stats) #:transparent
        #:methods gen:equal+hash
        [(define equal-proc spectral-equal?)
         (define hash-proc spectral-hash)
         (define hash2-proc spectral-hash2)])

(define empty-map (spectral (hash) (hash) (hash)))
(define-syntax-rule (sp-new-map) empty-map)

(define (sp-map-ref m k [default (λ () (error 'map-ref "Unmapped key ~a" k))])
  (match m
    [(spectral s m f _) (or (hash-ref s k #f)
                            (hash-ref m k #f)
                            (hash-ref f k default))]
    [_ (error 'sp-map-ref "Bad match ~a" m)]))

(define (sp-map-join-key m k av)
  ???)

(define (sp-map-overlap m0 m1)
  ???)

(define-syntax-rule (with-spectral-heap . rest-body)
  (splicing-syntax-parameterize
      ([new-map (make-rename-transformer #'sp-new-map)]
       [map-ref (make-rename-transformer #'sp-map-ref)]
       [map-join-key (make-rename-transformer #'sp-map-join-key)]
       [map-overlap (make-rename-transformer #'sp-map-overlap)])
    . rest-body))