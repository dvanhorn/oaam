#lang racket
(require racket/stxparam racket/trace)
(provide graph-file dump-dot add-edge! generate-graph?
         ev-state! co-after-var-state! reset-kind! state-kind)
;; for destination for *.dot files
(define graph-file (make-parameter #f))
(define state-kind #f) (define (reset-kind!) (set! state-kind #f))
(define (ev-state!) (set! state-kind 'ev))
(define (co-after-var-state!) (set! state-kind 'co-after-var))

(define-syntax-parameter generate-graph? #t)

(struct ev (s) #:transparent)
(struct cov (s) #:transparent)
(struct other (s) #:transparent)
(define (tag-kind s)
  (case state-kind
    [(ev) (ev s)]
    [(co-after-var) (cov s)]
    [else (other s)]))
(define (untag s)
  (match s
    [(or (ev s) (cov s) (other s)) s]
    [s s]))

(define (add-edge! g from to)
  (hash-set! g from (set-add (hash-ref g from (set)) (tag-kind to))))

;; The given graph will be from states to sets of states.
;; Rename states with symbols for node names.
(define (symbolize-graph graph ev-var? ev? co? compiled?)
  (define names (make-hash))
  (define nodes (make-hash))
  (define (cov-state? s)
    (and (co? s)
         (if compiled?
             (for*/or ([(from tos) (in-hash graph)]
                       [to (in-set tos)])
               (and (cov? to) (equal? (untag to) s)))
             (for*/or ([(from tos) (in-hash graph)]
                       #:when (ev-var? from)
                       [to (in-set tos)])
               (equal? (untag to) s)))))
  (define (name-of s) (hash-ref! names (untag s)
                                 (λ _ (define n (gensym 'n))
                                    (hash-set! nodes n (untag s))
                                    n)))
  (define (node-of n)
    (hash-ref nodes n
              (λ () (error 'symbolize-graph "Name unmapped ~a~%~a~%~a" n names nodes))))
  (begin0
   (for/hash ([(from tos) (in-hash graph)])
     (values (name-of from) (for/set ([to (in-set tos)]) (name-of to))))
   (for ([n (hash-values names)])
     (define s (node-of n))
     (printf "  ~a [label = \"\", style = filled, fillcolor = ~a];~%"
             n
             (cond [(cov-state? s) "gray"]
                   [(ev? s) "black"]
                   [else "white"])))))

(define (dump-dot graph ev-var? ev? co? compiled?)
  (with-output-to-file (graph-file) #:mode 'text #:exists 'replace
    (λ ()
       (printf "digraph Foo {~%")
       (for* ([(from adj) (in-hash (symbolize-graph graph ev-var? ev? co? compiled?))]
              [to (in-set adj)])
         (printf "  ~a -> ~a ;~%" from to))
       (printf "~%}"))))
