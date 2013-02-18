#lang racket
(require "../../r-tree/pure-sparse-r-tree.rkt"
         racket/splicing racket/trace
         "parameters.rkt"
         "data.rkt")
(provide with-rtree-nnmapc)

;; The r-tree keeps proximity information easily queriable, but not
;; direct lookups. We use a mutable hash for that.
(define map-data #f)

(define (r-new-map-map)
  (set! map-data (make-hash))
  empty)

(define (r-map-map-ref mm m [default (λ () (error 'map-map-ref "Unmapped map ~a" m))])
  (hash-ref map-data m default))

(define-syntax-rule (with-rtree-nnmapc . rest-body)
  (begin
    (define (r-map-map-add! mm m v)
      (define sh (map-boundary m))
      (define h (map-store m))
      (match (hash-ref map-data m #f)
        [#f
         (define m-hash (make-hasheq))
         (hash-set! map-data m m-hash)
         (hash-set! m-hash v #t)
         (insert mm (cons h m-hash) sh)]
        [m-hash
         (hash-set! m-hash v #t)
         mm]))

    (define (r-map-map-close mm m accept)
      (define hrect (map-boundary m))
      (define in-h (map-store m))
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

    (splicing-syntax-parameterize
        ([new-map-map (make-rename-transformer #'r-new-map-map)]
         [map-map-ref (make-rename-transformer #'r-map-map-ref)]
         [map-map-close (make-rename-transformer #'r-map-map-close)]
         [map-map-add! (make-rename-transformer #'r-map-map-add!)]
         [in-map-map-values (make-rename-transformer #'in-hash-keys)])
      . rest-body)))
