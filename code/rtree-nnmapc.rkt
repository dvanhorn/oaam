#lang racket
(require "../../r-tree/pure-sparse-r-tree.rkt"
         racket/splicing racket/trace
         "nnmapc.rkt"
         "data.rkt")
(provide with-rtree-nnmapc)
(struct boxed-hash (hrect map) #:prefab)
(define empty-map (boxed-hash #hash() #hash()))
(define (r-new-map) empty-map)
(define (r-map-ref m k [default (λ () (error 'map-ref "Unmapped key ~a" k))])
  (hash-ref (boxed-hash-map m) k default))

;; The r-tree keeps proximity information easily queriable, but not
;; direct lookups. We use a mutable hash for that.
(define map-data #f)

(define (r-new-map-map)
  (set! map-data (make-hash))
  empty)
(define (r-map-map-add! mm m v)
  (match-define (boxed-hash sh h) m)
  (match (hash-ref map-data m #f)
    [#f
     (define m-hash (make-hasheq))
     (hash-set! map-data m m-hash)
     (hash-set! m-hash v #t)
     (insert mm (cons h m-hash) sh)]
    [m-hash
     (hash-set! m-hash v #t)
     mm]))

(define (r-map-map-ref mm m [default (λ () (error 'map-map-ref "Unmapped map ~a" m))])
  (hash-ref map-data m default))

(define (r-map-map-close mm m accept)
  (match-define (boxed-hash hrect in-h) m)
  (define-values (_ max-overlap max-out0 max-out1)
    (for/fold ([max-good #f]
               [max-overlap #f]
               [max-out0 #f]
               [max-out1 #f])
        ([pair (in-list (find mm hrect))])
      (match-define (cons h m-hash) pair)
      (define overlap (map-overlap h in-h))
      (define-values (out0 out1) (accept h overlap m-hash))
      (if (and out0
               (or (not max-overlap)
                   (< (set-count max-overlap) (set-count overlap))))
          (values h overlap out0 out1)
          (values max-good max-overlap max-out0 max-out1))))
  (values max-overlap max-out0 max-out1))

(define-syntax-rule (with-rtree-nnmapc . rest-body)
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
         [new-map-map (make-rename-transformer #'r-new-map-map)]
         [map-map-ref (make-rename-transformer #'r-map-map-ref)]
         [map-map-close (make-rename-transformer #'r-map-map-close)]
         [map-map-add! (make-rename-transformer #'r-map-map-add!)]
         [in-map-map-values (make-rename-transformer #'in-hash-keys)]
         [map-overlap (make-rename-transformer #'s-map-overlap)])
      . rest-body)))
