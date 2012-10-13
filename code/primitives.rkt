#lang racket

(require "data.rkt"
         (for-syntax racket/list))
(provide mk-error-or-dispatch
         primitive?
         changes-store? reads-store? primitive?
         mk-prim-meaning)

(module prims racket
  (require (for-syntax syntax/parse racket/base))
  (provide mk-prim-meaning z s p b any)
  (define-values (z s p b any) (values #f #f #f #f #f))
  (define-for-syntax (type-match t v)
    #`(let ([v #,v])
        #,(case t
            [(z) #'(or (number? v) (eq? v 'number))]
            [(s) #'(or (string? v) (eq? v 'string))]
            [(!) #'(void? v)]
            [(b) #'(boolean? v)]
            [(v) #'(vectorv? v)]
            [(p) #'(consv? v)]
            [(any) #'#t])))
  (define-for-syntax (mk-checker ts [rest #f])
    #`(λ (vs) (and #,(if rest
                       #'(>= (length vs) #,(length ts))
                       #'(= (length vs) #,(length ts)))
                   #,@(for/list ([t (in-list ts)]
                                 [i (in-naturals)])
                        (type-match t #`(list-ref vs #,i)))
                   #,@(if rest
                        #`((for/and ([v (in-list (drop vs #,(length ts)))])
                            #,(type-match rest #'v)))
                        '()))))
  (define-syntax (mk-prim-meaning stx)
    (define-syntax-class basic #:literals (z s p b any) #:attributes (type)
      (pattern (~and (~or z s p b any) name) #:attr type (syntax-e #'name)))
    (define-syntax-class flat #:literals (->) #:attributes (checker-fn)
      (pattern (ts:basic ... (~optional (~seq #:rest r:basic)) -> t:basic)
               #:attr checker-fn (mk-checker (attribute ts.type) (attribute r.type))))
    (define-syntax-class type
      #:attributes (checker-fn)
      (pattern f:flat #:attr checker-fn (attribute f.checker-fn))
      (pattern (fs:flat ...)
               #:attr checker-fn
               #`(λ (vs) (or #,@(for/list ([f (in-list (attribute fs.checker-fn))])
                                  #`(#,f vs))))))
    (syntax-parse stx
      [(_ (~optional (~and #:static static?)) getter setter widen table-id:id)
       #`(begin
           #,(if (attribute static?)
               #'(...
                  (define-syntax-rule (define-types defines ... ([prim read-store? write-store? meaning t:type] ...))
                    (begin
                    (define table-id
                        (make-hasheq '((prim read-store? write-store?) ...)))
                    (define (mk-mk-check-good stx)
                      (syntax-case stx ()
                        [(_ check-good) (syntax/loc stx
                                          (define (check-good o vs)
                                            (case o [(prim) (t.checker-fn vs)] ...)))]))
                    (provide table-id mk-mk-check-good))))
               #'(...
                  (define-syntax-rule (define-types defines ... ([prim read-store? write-store? meaning type] ...))
                    (define table-id
                      (let ()
                        defines ...
                        (make-hasheq `((prim . ,meaning) ...)))))))
           (define-types
             (define both '(#t #f))
             (define-syntax-rule (both-if pred) (if pred both '(#f)))
             (define (equalv? σ v0 v1)
               (match* (v0 v1)
                 [((? clos?) _) (both-if (clos? v1))] ;; FIXME: not right for concrete
                 [(_ (? clos?)) '(#f)] ;; first not a closure
                 [((? consv?) _) (both-if (consv? v1))] ;; FIXME: not right for concrete
                 [(_ (? consv?)) '(#f)] ;; first not a cons
                 [((? vectorv?) _) (both-if (vectorv? v1))] ;; FIXME: not right for concrete
                 [(_ (? vectorv?)) '(#f)] ;; first not a vector
                 [((? primop?) _) `(,(equal? v0 v1))]
                 [(_ (? primop?)) '(#f)] ;; first not a primop
                 [((? number?) _) (cond [(eq? 'number v1) both]
                                        [(number? v1) `(,(= v0 v1))]
                                        [else '(#f)])]
                 [('number _) (both-if (or (eq? 'number v1) (number? v1)))]
                 [(_ 'number) '(#f)]
                 [((? string?) _) (cond [(eq? 'string v1) both]
                                        [(string? v1) `(,(string=? v0 v1))]
                                        [else '(#f)])]
                 [('string _) (both-if (or (eq? 'string v1) (string? v1)))]
                 [(_ 'string) '(#f)]
                 [((? symbol?) _) (cond [(eq? 'symbol v1) both]
                                        [(symbol? v1) `(,(eq? v0 v1))]
                                        [else '(#f)])]
                 [('symbol _) (both-if (or (eq? 'symbol v1) (symbol? v1)))]
                 [((? boolean?) _) `(,(equal? v0 v1))]
                 [('() _) `(,(eq? '() v1))]
                 [(_ '()) '(#f)]
                 [((? void?) _) `(,(void? v1))]
                 [(_ (? void?)) '(#f)]
                 [(_ _) (error 'equalv? "Incomplete match ~a ~a" v0 v1)]))
             (define (vectorv-ref σ vec z)
               (match vec
                 [(vectorv _ '()) '()]
                 [(vectorv _ (? list? l))
                  ;; sloppy. Abstract ref could get stuck, but just join all addrs.
                  (cond [(eq? 'number z)
                         (error 'vectorv-ref "Abstract vectors should have a single cell")]
                        [(or (< z 0) (>= z (length l))) '()]
                        [else (getter σ (list-ref l z))])]
                 [(vectorv _ abs-cell) (getter abs-cell)]))
             (define (vectorv-set! σ l δ vec i val)
               (match vec
                 [(vectorv _ '()) (values σ '())]
                 [(vectorv _ (? list? l))
                  (cond [(eq? 'number i)
                         (error 'vectorv-set! "Abstract vectors should have a single cell")]
                        [(or (< z 0) (>= z (length l))) (values σ '())]
                        [else (values (setter σ (list-ref l i) val) (void))])]
                 [(vectorv _ abs-cell) (setter σ abs-cell val)]))
             (define (add1v n)
               (if (eq? 'number n)
                 '(number)
                 `(,(widen (add1 n)))))
             (define (sub1v n)
               (if (eq? 'number n)
                 '(number)
                 `(,(widen (sub1 n)))))
             (define (zero?v n)
               (if (eq? 'number n)
                 both
                 `(,(zero? n))))
             (define (make-consv σ l δ v0 v1)
               (define A-addr `((A . ,l) . ,δ))
               (define D-addr `((D . ,l) . ,δ))
               (define σ*  (setter σ A-addr v0))
               (define σ** (setter σ D-addr v1))
               (values σ** `(,(consv A-addr D-addr))))
             (define (make-vectorv σ l δ size)
               (match (widen size)
                 ['number
                  (define V-addr `((V . ,l) . ,δ))
                  (define σ* (setter σ V-addr 0))
                  (values σ* (vectorv^ size V-addr))]
                 [_ (define V-addrs (for/list ()))]))
             (define (consv-car* σ v) (delay σ (consv-car v)))
             (define (consv-cdr* σ v) (delay σ (consv-cdr v)))
             ;; Booleans are for reads-store? writes-store?
             ((add1        #f #f add1v        (z -> z))
              (sub1        #f #f sub1v        (z -> z))
              (zero?       #f #f zero?v       (z -> b))
              (not         #f #f not          (any -> b))
              (*           #f #f *            (z z -> z))
              (+           #f #f +            (z z -> z))
              (-           #f #f -            (z z -> z))
              (=           #f #f =            (z z -> b))
              (equal?      #t #f equalv?      (any any -> b))
              (eqv?        #t #f equalv?      (any any -> b))
              (eq?         #t #f equalv?      (any any -> b))
              (vector?     #f #f vectorv?     (any -> b))
              (pair?       #f #f consv?       (any -> b))
              (vector-ref  #t #f vectorv-ref  (v z -> any))
              (vector-set! #f #t vectorv-set! (v z any -> !))
              (make-vector #f #t make-vectorv ((z -> v)
                                               (z any -> v)))
              ;; should be '() or p, but not expressible nor needed yet.
              (list        #f #t make-list    (#:rest any -> any))
              (cons        #f #t make-consv   (any any -> p))
              (car         #t #f consv-car*   (p -> any))
              (cdr         #t #f consv-car*   (p -> any)))))]))
    (mk-prim-meaning #:static _ _ _ prim-static))

(require (for-syntax 'prims) 'prims)

(define-syntax (mk-primitive-fns stx)
  (syntax-case stx ()
    [(_ primitive? check-good changes-store? reads-store?)
     (let ([prims (hash-keys prim-static)])
       (with-syntax ([(prim ...) prims]
                     [(store-changes ...)
                      (for/list ([p (in-list prims)])
                        (second (hash-ref prim-static p)))]
                     [(store-reads ...)
                      (for/list ([p (in-list prims)])
                        (first (hash-ref prim-static p)))])
         #`(begin (define (primitive? o)
                    (case o [(prim) #t] ... [else #f]))
                  (define (changes-store? o)
                    (case o [(prim) store-changes] ...))
                  (define-syntax mk-check-good mk-mk-check-good)
                  (mk-check-good check-good)
                  (define (reads-store? o)
                    (case o [(prim) store-reads] ...)))))]))

(mk-primitive-fns primitive? check-good changes-store? reads-store?)

(define-syntax-rule (mk-error-or-dispatch prim-meaning prim-meaning-table)
  (define (prim-meaning o vs)
    (cond [(check-good o vs) ((hash-ref prim-meaning-table o) vs)]
          [else '()])))
