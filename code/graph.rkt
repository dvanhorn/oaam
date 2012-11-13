#lang racket
(provide graph-file dump-dot add-edge!)
;; for destination for *.dot files
(define graph-file (make-parameter #f))

(define (add-edge! g from to)
  (hash-set! g from (set-add (hash-ref g from (set)) to)))

;; The given graph will be from states to sets of states.
;; Rename states with symbols for node names.
(define (symbolize-graph graph)
  (define names (make-hash))
  (define (name-of s) (hash-ref! names s (λ _ (gensym 'n))))
  (for/hash ([(from tos) (in-hash graph)])
    (values (name-of from) (for/set ([to (in-set tos)]) (name-of to)))))

(define (dump-dot graph)
  (define symb (symbolize-graph graph))
  (with-output-to-file (graph-file) #:mode 'text #:exists 'replace
    (λ ()
       (display "digraph Foo {") (newline)
       (for* ([(from adj) (in-hash symb)]
              [to (in-set adj)])
         (printf "  ~a -> ~a ;~%" from to))
       (newline) (display "}"))))
