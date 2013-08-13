#lang racket
(require racket/stxparam racket/trace
         (for-meta 2 racket/base))
(provide graph-file dump-dot add-edge! generate-graph?
         (for-syntax if-graph)
         ev-state!
         co-after-var-state!
         ap-after-call-state!
         chk-after-ret-state!
         reset-kind! state-kind)
;; for destination for *.dot files
(define graph-file (make-parameter #f))
(define state-kind #f) (define (reset-kind!) (set! state-kind #f))
(define (ev-state!) (set! state-kind 'ev))
(define (co-after-var-state!) (set! state-kind 'co-after-var))
(define (ap-after-call-state!) (set! state-kind 'ap-after-call))
(define (chk-after-ret-state!) (set! state-kind 'chk-after-ret))

(define-syntax-parameter generate-graph? #f)
(begin-for-syntax
 (define-syntax (if-graph stx)
   (syntax-case stx ()
     [(_ t) #'(if (syntax-parameter-value #'generate-graph?)
                  (list t)
                  '())]
     [(_ t e) #'(if (syntax-parameter-value #'generate-graph?)
                    (list t)
                    (list e))])))

(struct ev (s) #:transparent)
(struct cov (s) #:transparent)
(struct apc (s) #:transparent)
(struct chr (s) #:transparent)
(struct other (s) #:transparent)
(define (tag-kind s)
  (case state-kind
    [(ev) (ev s)]
    [(co-after-var) (cov s)]
    [(ap-after-call) (apc s)]
    [(chk-after-ret) (chr s)]
    [else (other s)]))
(define (untag s)
  (match s
    [(or (apc s) (chr s) (ev s) (cov s) (other s)) s]
    [s s]))

(define (add-edge! g from to)
  (hash-set! g from (set-add (hash-ref g from (set)) (tag-kind to))))

;; The given graph will be from states to sets of states.
;; Rename states with symbols for node names.
(define (symbolize-graph graph ev-var? ev? co? compiled?)
  (define names (make-hash))
  (define nodes (make-hash))
  (define (tagged-as pred s)
    (for*/or ([(from tos) (in-hash graph)]
              [to (in-set tos)])
      (and (pred to) (equal? (untag to) s))))
  (define (cov-state? s)
    (and (co? s)
         (if compiled?
             (tagged-as cov? s)
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
  
  (values
   (for/hash ([(from tos) (in-hash graph)])
     (values (name-of from) (for/set ([to (in-set tos)]) (name-of to))))
   (λ ()
      (for ([n (hash-values names)])
        (define s (node-of n))
        (define label?
          (or (tagged-as apc? s) (tagged-as chr? s)
              ;; throw in self-loops too.
              (for/or ([tn (in-set (hash-ref graph s (set)))]) (equal? s (untag tn)))))
        (printf "  ~a [label = \"~a\", style = filled, fillcolor = ~a];~%"
                n
                (if label?
                    (string-replace (with-output-to-string (λ () (pretty-print s)))
                                 "\n" "\\n")
                    "")
                (cond [(cov-state? s) "gray"]
                      [(tagged-as apc? s) "blue"]
                      [(tagged-as chr? s) "green"]
                      [(ev? s) "black"]
                      [else "white"]))))))

(define (dump-dot graph ev-var? ev? co? compiled?)
  (define-values (edges output-edges)
    (symbolize-graph graph ev-var? ev? co? compiled?))
  (with-output-to-file (graph-file) #:mode 'text #:exists 'replace
    (λ ()
       (printf "digraph Foo {~%")
       (output-edges)
       (for* ([(from adj) (in-hash edges)]
              [to (in-set adj)])
         (printf "  ~a -> ~a ;~%" from to))
       (printf "~%}"))))
