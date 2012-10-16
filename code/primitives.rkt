#lang racket

(require "data.rkt"
         (for-syntax racket/list racket/base))
(provide primitive? changes-store? reads-store? primitive?
         mk-prim-meaning)

(module prims racket
  (require (for-syntax syntax/parse racket/base) "data.rkt" "notation.rkt"
           syntax/parse/define
           racket/unsafe/ops)
  (provide mk-prim-meaning z s p b any)
  (define-values (z s p b v any !) (values #f #f #f #f #f #f #f))

  (define-for-syntax (type-match t v)
    #`(let ([v #,v])
        #,(case t
            [(z) #'(or (number? v) (eq? v 'number))]
            [(s) #'(or (string? v) (eq? v 'string))]
            [(!) #'(void? v)]
            [(b) #'(boolean? v)]
            [(v) #'(or (vectorv? v) (vectorv^? v))]
            [(p) #'(consv? v)]
            [(any) #'#t])))

  (define-for-syntax (mk-checker ts [rest #f])
    #`(λ (vs) (and #,(if rest
                       #`(>= (length vs) #,(length ts))
                       #`(= (length vs) #,(length ts)))
                   #,@(for/list ([t (in-list ts)]
                                 [i (in-naturals)])
                        (type-match t #`(list-ref vs #,i)))
                   #,@(if rest
                        #`((for/and ([v (in-list (drop vs #,(length ts)))])
                             #,(type-match rest #'v)))
                        '()))))
  (begin-for-syntax
    (define-syntax-class basic #:literals (z s p b v any !) #:attributes (type)
      (pattern (~and (~or z s p b v any !) name) #:attr type (syntax-e #'name)))
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
    (provide type))

  (define-syntax (mk-prim-meaning stx)
    (syntax-parse stx
      [(_ (~optional (~and #:static static?)) getter setter widen delay def-id:id)
       #`(begin
           #,(if (attribute static?)
               #'(...
                  (define-syntax (define-types stx)
                    (syntax-parse stx
                      [(_ td:id defines ... ([prim read-store? write-store? meaning t:type] ...))
                       #'(define td
                           (make-hasheq '((prim read-store? write-store?) ...)))]
                      [(_ defines ... ([x0 x1 x2 x3 x4] ...)) (raise-syntax-error #f "Bad type decls" stx)])))
               #'(...
                  (define-syntax (define-types stx)
                    (syntax-parse stx
                      [(_ td:id defines ... ([prim read-store? write-store? meaning t:type] ...))
                       #'(begin
                           defines ...
                           (define-syntax-rule (td o σ l δ vs)
                             (case o
                               [(prim) (if (t.checker-fn vs)
                                         (cond [write-store? (meaning σ l δ vs)]
                                               [read-store (meaning σ vs)]
                                               [else (meaning vs)])
                                         ;; XXX: Really void?
                                         '(void))] ...)))]
                      [(_ defines ... ([x0 x1 x2 x3 x4] ...)) (raise-syntax-error #f "Bad type decls" stx)]))))
           (define-types def-id
             (... (define-simple-macro (define/read (name:id σ:id v:id ...) body ...+)
                    (define (name σ vs) (match-define (list v ...) vs) body ...)))
             (... (define-simple-macro (define/write (name:id σ:id l:id δ:id v:id ... [opv:id opval:expr] ...) body ...+)
                    (define (name σ l δ vs)
                      (match-define (list-rest v ... rest) vs)
                      #,@(let ([defvs (length (syntax->list #'(opval ...)))])
                           (if (zero? defvs)
                             #'()
                             #'((define rest-len (length rest))
                                (define rest* (for/vector #:length #,defvs
                                                          ([v (in-list rest)]) v))
                                ;; Populate the rest of the default arguments with w
                                (for ([v (in-list (drop (list opval ...) rest-len))]
                                      [i (in-naturals rest-len)])
                                  (unsafe-vector-set! rest* i v))
                                (define-values (opv ...)
                                  (values #,@(for/list ([i (in-range defvs)])
                                               #`(unsafe-vector-ref rest* #,i)))))))
                      body ...)))
             (define both '(#t #f))
             ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
             ;; Prims that don't need the store
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
             (define (wide-num fn)
               (λ vs
                 `(,(widen (apply fn (filter-not (λ (x) (eq? x 'number)) vs))))))
             (define *v (wide-num *))
             (define +v (wide-num +))
             (define -v (wide-num -))
             (define =v (wide-num =))
             (define (vectorv*? v) `(,(or (vectorv? v) (vectorv^? v))))
             (define (consv*? v) `(,(consv? v)))
             (define (numberv? v) `(,(or (number? v) (eq? 'number v))))
             (define (stringv? v) `(,(or (string? v) (eq? 'string v))))
             (define (symbolv? v) `(,(or (symbol? v) (eq? 'symbol v))))
             (define (nullv? v) `(,(null? v)))
             (define (procedurev? v) `(,(clos? v)))
             (define (voidv? v) `(,(void? v)))
             (define (errorv . vs) '())

             (define (notv v) `(,(not v)))
             (define (voidv) `(,(void)))
             (define (vectorv-length v)
               (match v
                 [(or (vectorv len _) (vectorv^ len _)) `(,len)]))

             ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
             ;; Prims that read the store
             (define/read (equalv? σ v0 v1)
               (define-syntax-rule (both-if pred) (if pred both '(#f)))
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
             (define/read (vectorv-ref σ vec z)
               (match vec
                 [(vectorv _ l)
                  ;; sloppy. Abstract ref could get stuck, but just join all addrs.
                  (cond [(eq? 'number z)
                         (error 'vectorv-ref "Abstract vectors should have a single cell")]
                        [(or (< z 0) (>= z (length l))) '()]
                        [else (for/list ([v (delay σ (list-ref l z))]) v)])]
                 [(vectorv^ _ abs-cell) (for/list ([v (delay σ abs-cell)]) v)]))

             (define (mk-cons-accessor which)
               (define dirs (cdr (reverse (cdr (string->list (symbol->string which))))))
               (λ (σ vs)
                 (let chase ([dirs dirs] [v (first vs)])
                   (match dirs
                     ['() `(,v)]
                     [(cons dir dirs)
                      (match v
                        [(consv a d)
                         (define addr (case dir [(#\a) a] [(#\d) d]))
                         (if (null? dirs)
                           (for/list ([v (delay σ addr)]) v)
                           (for/append ([v (getter σ addr)])
                             (chase dirs v)))]
                        [_ '()])]))))
             ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
             ;; Prims that write the store
             (define/write (vectorv-set! σ l δ vec i val)
               (match vec
                 [(vectorv _ l)
                  (cond [(eq? 'number i)
                         (error 'vectorv-set! "Abstract vectors should have a single cell")]
                        [(or (< z 0) (>= z (length l))) (values σ '())]
                        [else (values (setter σ (list-ref l i) val) `(,(void)))])]
                 [(vectorv^ _ abs-cell) (values (setter σ abs-cell val) `(,(void)))]))

             (define/write (make-vectorv σ l δ size [default 0])
               (match (widen size)
                 ['number
                  (define V-addr `((V . ,l) . ,δ))
                  (define σ* (setter σ V-addr default))
                  (values σ* `(,(vectorv^ size V-addr)))]
                 [_ (define V-addrs
                      (for/list ([i (in-range size)]) `((V ,i . ,l) . ,δ)))
                    (define σ* (for/fold ([σ σ]) ([a (in-list V-addrs)])
                                 (setter σ a default)))
                    (values σ* `(,(vectorv size V-addrs)))]))

             (define/write (make-consv σ l δ v0 v1)
               (define A-addr `((A . ,l) . ,δ))
               (define D-addr `((D . ,l) . ,δ))
               (define σ*  (setter σ A-addr v0))
               (define σ** (setter σ* D-addr v1))
               (values σ** `(,(consv A-addr D-addr))))

             (define/write (set-car!v σ l δ p v)
               (values (setter σ (consv-car p) v) `(,(void))))
             (define/write (set-cdr!v σ l δ p v)
               (values (setter σ (consv-cdr p) v) `(,(void))))

             (define/write (make-listv σ l δ . vs)
               (cond [(null? vs) (values σ '(()))]
                     [else
                      (define (laddr i)
                        (values `((L ,i . ,l) . ,δ) `((L ,i D . ,l) . ,δ)))
                      (define-values (fst-addr snd-addr) (laddr 0))
                      (define val (consv fst-addr snd-addr))
                      (let loop ([σ (setter σ fst-addr (first vs))]
                                 [last-addr snd-addr]
                                 [vs (rest vs)]
                                 [i 1])
                        (cond [(null? vs) (values (setter σ last-addr '()) `(,val))]
                              [else
                               (define-values (fst-addr snd-addr) (laddr i))
                               (define σ*  (setter σ  fst-addr  (first vs)))
                               (define σ** (setter σ* last-addr (consv fst-addr snd-addr)))
                               (loop σ** snd-addr (rest vs) (add1 i))]))]))

             ;; Booleans are for reads-store? writes-store?
             ((add1          #f #f add1v          (z -> z))
              (sub1          #f #f sub1v          (z -> z))
              (zero?         #f #f zero?v         (z -> b))
              (not           #f #f notv           (any -> b))
              (*             #f #f *v             (#:rest z -> z))
              (+             #f #f +v             (#:rest z -> z))
              (-             #f #f -v             (#:rest z -> z))
              (=             #f #f =v             (#:rest z -> b))
              (equal?        #t #f equalv?        (any any -> b))
              (eqv?          #t #f equalv?        (any any -> b))
              (eq?           #t #f equalv?        (any any -> b))
              ;; vector ops
              (vector?       #f #f vectorv*?      (any -> b))
              (vector-ref    #t #f vectorv-ref    (v z -> any))
              (vector-set!   #f #t vectorv-set!   (v z any -> !))
              [vector-length #f #f vectorv-length (v -> z)]
              [make-vector   #f #t make-vectorv   ((z -> v)
                                                   (z any -> v))]
              ;; should be '() or p, but not expressible nor needed yet.
              [list        #f #t make-listv (#:rest any -> any)]
              [null?       #f #f nullv?     (any -> b)]
              [pair?       #f #f consv*?    (any -> b)]
              [cons        #f #t make-consv (any any -> p)]
              [car         #t #f (mk-cons-accessor 'car)    (p -> any)]
              [cdr         #t #f (mk-cons-accessor 'cdr)    (p -> any)]
              [caar        #t #f (mk-cons-accessor 'caar)   (p -> any)]
              [cadr        #t #f (mk-cons-accessor 'cadr)   (p -> any)]
              [cdar        #t #f (mk-cons-accessor 'cdar)   (p -> any)]
              [cddr        #t #f (mk-cons-accessor 'cddr)   (p -> any)]
              [caaar       #t #f (mk-cons-accessor 'caaar)  (p -> any)]
              [caadr       #t #f (mk-cons-accessor 'caadr)  (p -> any)]
              [cadar       #t #f (mk-cons-accessor 'cadar)  (p -> any)]
              [caddr       #t #f (mk-cons-accessor 'caddr)  (p -> any)]
              [cdaar       #t #f (mk-cons-accessor 'cdaar)  (p -> any)]
              [cdadr       #t #f (mk-cons-accessor 'cdadr)  (p -> any)]
              [cddar       #t #f (mk-cons-accessor 'cddar)  (p -> any)]
              [cdddr       #t #f (mk-cons-accessor 'cdddr)  (p -> any)]
              [caaaar      #t #f (mk-cons-accessor 'caaaar) (p -> any)]
              [caaadr      #t #f (mk-cons-accessor 'caaadr) (p -> any)]
              [caadar      #t #f (mk-cons-accessor 'caadar) (p -> any)]
              [caaddr      #t #f (mk-cons-accessor 'caaddr) (p -> any)]
              [cadaar      #t #f (mk-cons-accessor 'cadaar) (p -> any)]
              [cadadr      #t #f (mk-cons-accessor 'cadadr) (p -> any)]
              [caddar      #t #f (mk-cons-accessor 'caddar) (p -> any)]
              [cadddr      #t #f (mk-cons-accessor 'cadddr) (p -> any)]
              [cdaaar      #t #f (mk-cons-accessor 'cdaaar) (p -> any)]
              [cdaadr      #t #f (mk-cons-accessor 'cdaadr) (p -> any)]
              [cdadar      #t #f (mk-cons-accessor 'cdadar) (p -> any)]
              [cdaddr      #t #f (mk-cons-accessor 'cdaddr) (p -> any)]
              [cddaar      #t #f (mk-cons-accessor 'cddaar) (p -> any)]
              [cddadr      #t #f (mk-cons-accessor 'cddadr) (p -> any)]
              [cdddar      #t #f (mk-cons-accessor 'cdddar) (p -> any)]
              [cddddr      #t #f (mk-cons-accessor 'cddddr) (p -> any)]
              ;; imperative ops
              [set-car!    #f #t set-car!v (p any -> !)]
              [set-cdr!    #f #t set-cdr!v (p any -> !)]
              [void        #f #f voidv     (-> !)]
              [error       #f #f errorv    (#:rest any -> any)])))]))

  (mk-prim-meaning #:static _ _ _ _ prim-static))
(require (for-syntax 'prims) 'prims)

(define-syntax (mk-primitive-fns stx)
  (syntax-case stx ()
    [(_ primitive? changes-store? reads-store?)
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
                  (define (reads-store? o)
                    (case o [(prim) store-reads] ...)))))]))

(mk-primitive-fns primitive? changes-store? reads-store?)
