#lang racket
(require racket/stxparam)
(provide graph-file dump-dot add-edge! generate-graph?)
;; for destination for *.dot files
(define graph-file (make-parameter #f))

(define-syntax-parameter generate-graph? #f)

(define (add-edge! g from to)
  (hash-set! g from (set-add (hash-ref g from (set)) to)))

;; The given graph will be from states to sets of states.
;; Rename states with symbols for node names.
(define (symbolize-graph graph)
  (define names (make-hash))
  (define (name-of s) (hash-ref! names s (λ _ (gensym 'n))))
  (begin0
   (for/hash ([(from tos) (in-hash graph)])
     (values (name-of from) (for/set ([to (in-set tos)]) (name-of to))))
   (for ([n (hash-values names)]) (printf "  ~a [label = \"\"];~%" n))))

(define (dump-dot graph)
  (with-output-to-file (graph-file) #:mode 'text #:exists 'replace
    (λ ()
       (printf "digraph Foo {~%")
       (for* ([(from adj) (in-hash (symbolize-graph graph))]
              [to (in-set adj)])
         (printf "  ~a -> ~a ;~%" from to))
       (printf "~%}"))))
