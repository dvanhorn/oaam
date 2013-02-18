#lang racket/base
(require "notation.rkt" racket/unsafe/ops "parameters.rkt"
         (for-syntax racket/base)
         "data.rkt" racket/splicing
         "simple-hash.rkt")
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

(define stable-joins-until-promotion 2)

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

;; Stats tracks how many stable joins happen to an address since level changes,
;; so when they pass a threshold an address can be promoted.
(struct spectral (slow medium fast stats) #:transparent
        #:methods gen:equal+hash
        [(define equal-proc spectral-equal?)
         (define hash-proc spectral-hash)
         (define hash2-proc spectral-hash2)])

(define empty-map (spectral (hash) (hash) (hash) (hash)))
(define-syntax-rule (sp-new-map) empty-map)

(define (sp-map-ref m k [default (λ () (error 'map-ref "Unmapped key ~a" k))])
  (match m
    [(spectral s m f _) (or (hash-ref s k #f)
                            (hash-ref m k #f)
                            (hash-ref f k default))]
    [_ (error 'sp-map-ref "Bad match ~a" m)]))

(define (sp-map-boundary) (error 'Spectral-non-spatial))
(define (sp-map-store) (error 'Spectral-non-spatial))

(define/match (sp-map-distance m0 m1)
  [((spectral s0 m0 f0 _) (spectral s1 m1 f1 _))
   (if (and (eq? s0 s1) (eq? m0 m1))
       (s-map-distance f0 f1)
       +inf.0)])

(define (s-map-key-set m [initial ∅])
  (for/fold ([acc initial])
      ([k (in-hash-keys m)])
    (∪1 acc k)))

(define/match (sp-map-overlap m0 m1)
  [((spectral s0 m0 f0 _) (spectral s1 m1 f1 _))
   (if (eq? s0 s1)
       (let ([skeys (s-map-key-set s0)])
         (if (eq? m0 m1)
             (let ([mkeys (s-map-key-set m0 skeys)])
               (if (eq? f0 f1)
                   (s-map-key-set f0 mkeys)
                   (∪ mkeys (s-map-overlap f0 f1))))
             (∪ skeys
                (if (eq? f0 f1)
                    (s-map-key-set f0 (s-map-overlap m0 m1))
                    (∪ (s-map-overlap m0 m1)
                       (s-map-overlap m0 f1)
                       (s-map-overlap f0 m1)
                       (s-map-overlap f0 f1))))))
       (if (eq? m0 m1)
           (if (eq? f0 f1)
               (s-map-key-set m0 (s-map-key-set f0 (s-map-overlap s0 s1)))
               (s-map-key-set m0 (∪ (s-map-overlap s0 s1)
                                    (s-map-overlap s0 f1)
                                    (s-map-overlap f0 s1)
                                    (s-map-overlap f0 f1))))
           (if (eq? f0 f1)
               (s-map-key-set f0 (∪ (s-map-overlap m0 m1)
                                    (s-map-overlap m0 s1)
                                    (s-map-overlap s0 m1)
                                    (s-map-overlap s0 s1)))
               (∪ (s-map-overlap s0 s1)
                  (s-map-overlap s0 m1)
                  (s-map-overlap s0 f1)
                  (s-map-overlap m0 s1)
                  (s-map-overlap m0 m1)
                  (s-map-overlap m0 f1)
                  (s-map-overlap f0 s1)
                  (s-map-overlap f0 m1)
                  (s-map-overlap f0 f1)))))])

(define-syntax-rule (with-spectral-heap . rest-body)
  (begin
    (define (sp-map-join-key sp k av)
      (match sp
        [(spectral s m f stats)
         (match (hash-ref s k #f)
           [#f
            (match (hash-ref m k #f)
              [#f
               (match (hash-ref f k #f)
                 [#f (spectral s m (hash-set f k av) (hash-set stats k 0))]
                 [kav
                  (define joined (⊓ av kav))
                  (define reset-stats (hash-set stats k 0))
                  (cond
                   [(≡ kav joined)
                    (define joins (add1 (hash-ref stats k)))
                    ;; Promote from fast to medium?
                    (if (>= joins stable-joins-until-promotion)
                        (spectral s (hash-set m k kav) (hash-remove f k) reset-stats)
                        (spectral s m f (hash-set stats k joins)))]
                   [else ;; Demote.
                    (spectral s (hash-remove m k) (hash-set f k joined) (hash-set stats k 0))])])]
              [kav
               (define joined (⊓ av kav))
               (define reset-stats (hash-set stats k 0))
               (cond
                [(≡ kav joined)
                 (define joins (add1 (hash-ref stats k)))
                 ;; Promote from medium to slow?
                 (if (>= joins stable-joins-until-promotion)
                     (spectral (hash-set s k kav) (hash-remove m k) f reset-stats)
                     (spectral s m f (hash-set stats k joins)))]
                [else ;; Demote.
                 (spectral s (hash-remove m k) (hash-set f k joined) reset-stats)])])]
           [kav
            (define joined (⊓ av kav))
            (if (≡ kav joined)
                sp
                (spectral (hash-remove s k) (hash-set m k joined) f (hash-set stats k 0)))])]
        [_ (error 'sp-map-join-key "Bad match ~a" sp)]))

  (splicing-syntax-parameterize
      ([new-map (make-rename-transformer #'sp-new-map)]
       [map-ref (make-rename-transformer #'sp-map-ref)]
       [map-join-key (make-rename-transformer #'sp-map-join-key)]
       [map-overlap (make-rename-transformer #'sp-map-overlap)]
       [map-distance (make-rename-transformer #'sp-map-distance)]
       [map-boundary (make-rename-transformer #'sp-map-boundary)]
       [map-store (make-rename-transformer #'sp-map-store)])
    . rest-body)))