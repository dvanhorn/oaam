#lang racket
(require racket/stxparam (for-syntax racket/stxparam))
(provide graph-file dump-dot add-edge! new-graph generate-graph?
         node-of node-of/data
         (struct-out node)
         (for-syntax when-graph if-graph))
;; for destination for *.dot files
(define graph-file (make-parameter #f))

(define-syntax-parameter generate-graph? #f)
(begin-for-syntax
 (define-syntax-rule (when-graph body ...)
   (if (syntax-parameter-value #'generate-graph?)
       #`(#,(let () body ...))
       #'()))
 (define-syntax-rule (if-graph then else)
   (if (syntax-parameter-value #'generate-graph?)
       then
       else)))

(struct node (state [succ #:mutable] [data #:mutable]) #:prefab)

(define (new-graph) (make-hash))
(define (node-of g state)
  (hash-ref! g state (λ () (node state (seteq) #f))))
(define-syntax-rule (node-of/data g state data)
  (hash-ref! g state (λ () (node state (seteq) data))))

(define (add-edge! g from to)
  (define from-n (node-of g from))
  (define to-n (node-of g to))
  (set-node-succ! g from-n (set-add (node-succ from-n) to-n)))

;; The given graph will be from states to sets of states.
;; Rename states with symbols for node names.
(define (symbolize-graph graph)
  (define names (make-hash))
  (define (name-of s) (hash-ref! names s (λ _ (gensym 'n))))
  (begin0
   (for/hash ([(from n) (in-hash graph)])
     (values (name-of n)
             (for/set ([to (in-set (node-succ n))])
               (name-of to))))
   (for ([n (hash-values names)]) (printf "  ~a [label = \"\"];~%" n))))

(define (dump-dot graph)
  (with-output-to-file (graph-file) #:mode 'text #:exists 'replace
    (λ ()
       (printf "digraph Foo {~%")
       (for* ([(from adj) (in-hash (symbolize-graph graph))]
              [to (in-set adj)])
         (printf "  ~a -> ~a ;~%" from to))
       (printf "~%}"))))
