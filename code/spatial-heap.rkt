#lang racket/base
(provide with-contextual-addressing)
;; Large heaps have to be compared for congruence in the contextual sparseness algorithm.
;; We take advantage of spatial locality in our representation of heaps in this module by
;; subdividing the heap into regions and subregions (etc.) that can be accessed by a lexical
;; scope path (slightly complexified by on-the-fly allocations).
;; Since large chunks of the heap are likely to remain unchanged when analyzing a specific region,
;; this subdivision allows for quick-to-succeed congruence tests via pointer equality of nodes
;; in the subdivision.

;; We can also cache ⊑ computations between nodes.

(struct address (alloc-ctx kind addr) #:prefab)
(define-syntax-rule (make-var-contour-0s l x δ) (address l 'var x))
(define-syntax-rule (make-intermediate-contour-0s l x δ) (address l 'temp x))
(define-syntax-rule (make-vector^-contour-0s l δ) (address l 'vector^ l))
(define-syntax-rule (make-vector-contour-0s l i δ) (address l 'vector i))
(define-syntax-rule (make-car-contour-0s l δ) (address l 'car l))
(define-syntax-rule (make-cdr-contour-0s l δ) (address l 'cdr l))
(define-syntax-rule (make-port-contour-0s l δ) (address l 'car l))
(define-syntax-rule (make-apply-contour-0s l n δ) (address l 'apply n))
(define-syntax-rule (make-kont-contour-0s l δ) (address l 'kont l))
(define-syntax-rule (make-rest^-contour-0s l δ) (address l 'rest-args l))
(define-syntax-rule (with-contextual-addressing . body)
  (splicing-syntax-parameterize
      ([make-var-contour (make-rename-transformer #'make-var-contour-0s)]
       [make-intermediate-contour (make-rename-transformer #'make-intermediate-contour-0s)]
       [make-vector^-contour (make-rename-transformer #'make-vector^-contour-0s)]
       [make-vector-contour (make-rename-transformer #'make-vector-contour-0s)]
       [make-car-contour (make-rename-transformer #'make-car-contour-0s)]
       [make-cdr-contour (make-rename-transformer #'make-cdr-contour-0s)]
       [make-port-contour (make-rename-transformer #'make-port-contour-0s)]
       [make-apply-contour (make-rename-transformer #'make-apply-contour-0s)]
       [make-kont-contour (make-rename-transformer #'make-kont-contour-0s)]
       [make-rest^-contour (make-rename-transformer #'make-rest^-contour-0s)])
    . body))

;; A spatial-hash is one of
;; - (internal label domain hash[label,spatial-hash])
;; - hash[address, abstract-values]
