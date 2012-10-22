#lang racket

(require "data.rkt" "notation.rkt" "do.rkt"
         (for-syntax syntax/parse racket/syntax
                     racket/list racket/base)
         racket/stxparam
         racket/unsafe/ops)
(provide primitive? changes-store? reads-store? primitive?
         mk-prims snull
         yield force getter widen delay)

(define-syntax-parameter getter #f)
(define-syntax-parameter force #f)
(define-syntax-parameter widen #f)
(define-syntax-parameter delay #f)
(define-syntax-parameter yield
  (λ (stx)
     (raise-syntax-error #f "Must be within the context of a generator" stx)))

;; Identifiers for the crappy type DSL
;; Meanings (respectively): Number String Pair Boolean Vector Any Void
(define-values (z s p b v any !) (values #f #f #f #f #f #f #f))

(define snull (set '()))

(begin-for-syntax
 (define (type-match t v)
   #`(let ([v #,v])
       #,(case t
           [(z) #'(or (number? v) (eq? v 'number))]
           [(s) #'(or (string? v) (eq? v 'string))]
           [(!) #'(void? v)]
           [(b) #'(boolean? v)]
           [(v) #'(or (vectorv? v) (vectorv^? v))]
           [(p) #'(consv? v)]
           [(any) #'#t])))

 (define (mk-checker ts [rest #f])
   #`(λ (vs)
        (and #,(if rest
                   #`(>= (length vs) #,(length ts))
                   #`(= (length vs) #,(length ts)))
             #,@(for/list ([t (in-list ts)]
                           [i (in-naturals)])
                  (type-match t #`(list-ref vs #,i)))
             #,@(if rest
                    #`((for/and ([v (in-list (drop vs #,(length ts)))])
                         #,(type-match rest #'v)))
                    '()))))
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
                               #`(#,f vs)))))))

(define-syntax (mk-static-primitive-functions stx)
  (syntax-parse stx
    [(_ primitive?:id changes-store?:id reads-store?:id
        ([prim:id read-store?:boolean write-store?:boolean _ _] ...))
     (syntax/loc stx
       (begin (define (primitive? o)
                (case o [(prim) #t] ... [else #f]))
              (define (changes-store? o)
                (case o [(prim) write-store?] ...))
              (define (reads-store? o)
                (case o [(prim) write-store?] ...))))]))

(define-syntax (mk-primitive-meaning stx)
  (syntax-parse stx
    [(_ mean:id defines ...
        ([prim read-store? write-store? meaning t:type] ...))
     (quasisyntax/loc stx
       (begin
         defines ...
         (define-syntax-rule (mean o σ l δ vs)
           (case o
             #,@(for/list ([p (in-list (syntax->list #'(prim ...)))]
                           [w? (in-list (syntax->datum #'(write-store? ...)))]
                           [r? (in-list (syntax->datum #'(read-store? ...)))]
                           [m (in-list (syntax->list #'(meaning ...)))]
                           [checker (in-list (attribute t.checker-fn))])
                  #`[(#,p)
                     (if (#,checker vs)
                         #,(cond [w? #`(#,m σ l δ vs)]
                                 [r? #`(#,m σ vs)]
                                 [else #`(#,m vs)])
                         (continue))])))))]))

(define-simple-macro* (define/read (name:id σ:id v:id ...) body ...+)
  ;; XXX: not capture-avoiding, so we have to be careful in our definitions
  (define-simple-macro* (name σ vs)
    (match vs
      [(list v ...) body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

(define-simple-macro* (define/basic (name:id v:id ...) body ...+)
  (define-simple-macro* (name vs)
    (match vs
      [(list v ...) body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

(define-simple-macro* (define/write (name:id σ:id l:id δ:id v:id ... [opv:id opval:expr] ...) body ...+)
  (define-simple-macro* (name σ l δ vs)
    (match vs
      [(list-rest v ... rest)
       #,@(let ([defvs (length (syntax->list #'(opval ...)))])
            (if (zero? defvs)
                #'()
                #`((define rest-len (length rest))
                   (define rest* (for/vector #:length #,defvs
                                             ([v* (in-list rest)]) v*))
                   ;; Populate the rest of the default arguments with w
                   (for ([v* (in-list (drop (list opval ...) rest-len))]
                         [i (in-naturals rest-len)])
                     (unsafe-vector-set! rest* i v*))
                   (define-values (opv ...)
                     (values #,@(for/list ([i (in-range defvs)])
                                  #`(unsafe-vector-ref rest* #,i)))))))
       body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

(define-syntax (mk-prims stx)
  (syntax-parse stx
    [(_ (~or (~seq (~and #:static static?) primitive?:id changes-store?:id reads-store?:id)
             (~seq mean:id clos?:id)))
     (if (attribute static?)
         (quasisyntax/loc stx
           (mk-static-primitive-functions
            primitive? changes-store? reads-store? #,prim-table))
         (quasisyntax/loc stx
           (mk-primitive-meaning mean #,@(prim-defines #'clos?) #,prim-table)))]))

(define-for-syntax (prim-defines clos?)
  (with-syntax ([clos? clos?])
    #'((define both '(#t #f))
       (define-simple-macro* (yield-both σ)
         ;; Do needs σ, but it's already bound by an outer do (if σ ever bound)
         ;; If not ever bound, just give a dummy identifier.
         (do (σ) ([b (in-list '(#t #f))]) (yield b)))
       (define-syntax-rule (yield-delay σ v)
         (do (σ) ([v* (delay σ v)]) (yield v*)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that don't need the store
       (define/basic (add1v n)
         (if (eq? 'number n)
             (yield 'number)
             (yield (widen (add1 n)))))
       (define/basic (sub1v n)
         (if (eq? 'number n)
             (yield 'number)
             (yield (widen (sub1 n)))))
       (define/read (zero?v σ n)
         (if (eq? 'number n)
             (yield-both σ)
             (yield (zero? n))))
       (define-simple-macro* (wide-num fn vs)
         (yield (widen (apply fn (filter-not (λ (x) (eq? x 'number)) vs)))))
       (define-simple-macro* (*v vs) (wide-num * vs))
       (define-simple-macro* (+v vs) (wide-num + vs))
       (define-simple-macro* (-v vs) (wide-num - vs))
       (define-simple-macro* (=v σ vs)
         (if (memv 'number vs)
             (yield-both σ)
             (yield (apply = vs))))
       (define/basic (vectorv*? v) (yield (or (vectorv? v) (vectorv^? v))))
       (define/basic (consv*? v) (yield (consv? v)))
       (define/basic (numberv? v) (yield (or (number? v) (eq? 'number v))))
       (define/basic (stringv? v) (yield (or (string? v) (eq? 'string v))))
       (define/basic (symbolv? v) (yield (or (symbol? v) (eq? 'symbol v))))
       (define/basic (booleanv? v) (yield (boolean? v)))
       (define/basic (nullv? v) (yield (null? v)))
       (define/basic (procedurev? v) (yield (clos? v)))
       (define/basic (voidv? v) (yield (void? v)))
       (define-simple-macro* (errorv vs) (continue))

       (define/basic (notv v) (yield (not v)))
       (define/basic (voidv) (yield (void)))
       (define/basic (vectorv-length v)
         (match v
           [(or (vectorv len _) (vectorv^ len _)) (yield len)]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that read the store
       (define/read (equalv? σ v0 v1)
         (define-syntax-rule (both-if pred) (if pred (yield-both σ) (yield #f)))
         (match* (v0 v1)
           [((? clos?) _) (both-if (clos? v1))] ;; FIXME: not right for concrete
           [(_ (? clos?)) (yield #f)]           ;; first not a closure
           [((? consv?) _) (both-if (consv? v1))] ;; FIXME: not right for concrete
           [(_ (? consv?)) (yield #f)]            ;; first not a cons
           [((? vectorv?) _) (both-if (vectorv? v1))] ;; FIXME: not right for concrete
           [(_ (? vectorv?)) (yield #f)] ;; first not a vector
           [((? primop?) _) (yield (equal? v0 v1))]
           [(_ (? primop?)) (yield #f)] ;; first not a primop
           [((? number?) _) (cond [(eq? 'number v1) (yield-both σ)]
                                  [(number? v1) (yield (= v0 v1))]
                                  [else (yield #f)])]
           [('number _) (both-if (or (eq? 'number v1) (number? v1)))]
           [(_ 'number) (yield #f)]
           [((? string?) _) (cond [(eq? 'string v1) (yield-both σ)]
                                  [(string? v1) (yield (string=? v0 v1))]
                                  [else (yield #f)])]
           [('string _) (both-if (or (eq? 'string v1) (string? v1)))]
           [(_ 'string) (yield #f)]
           [((? symbol?) _) (cond [(eq? 'symbol v1) (yield-both σ)]
                                  [(symbol? v1) (yield (eq? v0 v1))]
                                  [else (yield #f)])]
           [('symbol _) (both-if (or (eq? 'symbol v1) (symbol? v1)))]
           [((? boolean?) _) (yield (equal? v0 v1))]
           [('() _) (yield (eq? '() v1))]
           [(_ '()) (yield #f)]
           [((? void?) _) (yield (void? v1))]
           [(_ (? void?)) (yield #f)]
           [(_ _) (error 'equalv? "Incomplete match ~a ~a" v0 v1)]))
       (define/read (vectorv-ref σ vec z)
         (match vec
           [(vectorv _ l)
            (cond [(eq? 'number z)
                   (error 'vectorv-ref "Abstract vectors should have a single cell")]
                  [(or (< z 0) (>= z (length l))) (continue)]
                  [else (yield-delay σ (list-ref l z))])]
           [(vectorv^ _ abs-cell) (yield-delay σ abs-cell)]))

       ;; TODO?: This could be compiled to have less interpreted overhead
       ;; Could cause too much code to be generated or cause unreadability
       (define-simple-macro* (mk-cons-accessor name which)
         (define-simple-macro* (name σ vs)
           (let ([dirs '#,(cdr (reverse (cdr (string->list (symbol->string (syntax-e #'which))))))])
             (do (σ) chase ([dirs dirs] [v (first vs)])
                 (match dirs
                   ['() (yield v)]
                   [(cons dir dirs)
                    (match v
                      [(consv a d)
                       (define addr (case dir [(#\a) a] [(#\d) d]))
                       (if (null? dirs)
                           (yield-delay σ addr)
                           (do (σ) ([v (getter σ addr)])
                             (chase σ dirs v)))]
                      [_ (continue)])])))))
       (mk-cons-accessor carv car)
       (mk-cons-accessor cdrv cdr)
       (mk-cons-accessor caarv caar)
       (mk-cons-accessor cadrv cadr)
       (mk-cons-accessor cdarv cdar)
       (mk-cons-accessor cddrv cddr)
       (mk-cons-accessor caaarv caaar)
       (mk-cons-accessor caadrv caadr)
       (mk-cons-accessor cadarv cadar)
       (mk-cons-accessor caddrv caddr)
       (mk-cons-accessor cdaarv cdaar)
       (mk-cons-accessor cdadrv cdadr)
       (mk-cons-accessor cddarv cddar)
       (mk-cons-accessor cdddrv cdddr)
       (mk-cons-accessor caaaarv caaaar)
       (mk-cons-accessor caaadrv caaadr)
       (mk-cons-accessor caadarv caadar)
       (mk-cons-accessor caaddrv caaddr)
       (mk-cons-accessor cadaarv cadaar)
       (mk-cons-accessor cadadrv cadadr)
       (mk-cons-accessor caddarv caddar)
       (mk-cons-accessor cadddrv cadddr)
       (mk-cons-accessor cdaaarv cdaaar)
       (mk-cons-accessor cdaadrv cdaadr)
       (mk-cons-accessor cdadarv cdadar)
       (mk-cons-accessor cdaddrv cdaddr)
       (mk-cons-accessor cddaarv cddaar)
       (mk-cons-accessor cddadrv cddadr)
       (mk-cons-accessor cdddarv cdddar)
       (mk-cons-accessor cddddrv cddddr)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that write the store
       (define/write (vectorv-set! σ l δ vec i val)
         (match vec
           [(vectorv _ addrs)
            (cond [(eq? 'number i)
                   (error 'vectorv-set! "Abstract vectors should have a single cell")]
                  [(or (< z 0) (>= z (length addrs))) (continue)]
                  [else (do (σ) ([σ*-vec #:join σ (list-ref addrs i) (force σ val)])
                          (yield (void)))])]
           [(vectorv^ _ abs-cell)
            (do (σ) ([σ*-vec^ #:join σ abs-cell (force σ val)])
              (yield (void)))]))

       (define/write (make-vectorv σ l δ size [default 0])
         (match (widen size)
           ['number
            (define V-addr (make-var-contour `(V . ,l) δ))
            (do (σ) ([σ*-mv^ #:join σ V-addr (force σ default)])
              (yield (vectorv^ size V-addr)))]
           [_ (define V-addrs
                (for/list ([i (in-range size)]) (make-var-contour `(V ,i . ,l) δ)))
              (do (σ) ([σ*-mv #:join* σ V-addrs (make-list size default)])
                (yield (vectorv size V-addrs)))]))

       (define/write (make-consv σ l δ v0 v1)
         (define A-addr (make-var-contour `(A . ,l) δ))
         (define D-addr (make-var-contour `(D . ,l) δ))
         (do (σ) ([σ*A #:join σ A-addr (force σ v0)]
                  [σ*D #:join σ*A D-addr (force σ*A v1)])
           (yield (consv A-addr D-addr))))

       (define/write (set-car!v σ l δ p v)
         (do (σ) ([σ*a! #:join σ (consv-car p) (force σ v)]) (yield (void))))
       (define/write (set-cdr!v σ l δ p v)
         (do (σ) ([σ*d! #:join σ (consv-cdr p) (force σ v)]) (yield (void))))

       (define-simple-macro* (make-listv σ l δ vs)
         (cond [(null? vs) (continue)]
               [else
                (define (laddr i)
                  (values (make-var-contour `(L ,i . ,l) δ)
                          (make-var-contour `(L ,i D . ,l) δ)))
                (define-values (fst-addr snd-addr) (laddr 0))
                (define val (consv fst-addr snd-addr))
                (do (σ) ([σ*ml #:join σ fst-addr (force σ (first vs))])
                  (do (σ*ml) loop ([last-addr snd-addr]
                                 [vs (rest vs)]
                                 [i 1])
                      (cond
                       [(null? vs)
                        (do (σ*ml) ([σ*mll #:join σ*ml last-addr snull])
                          (yield val))]
                       [else
                        (define-values (fst-addr snd-addr) (laddr i))
                        (do (σ*ml) ([σ*mlf #:join σ*ml fst-addr (force σ*ml (first vs))]
                                    [σ*mln #:join σ*mlf last-addr (set (consv fst-addr snd-addr))])
                          (loop σ*mln snd-addr (rest vs) (add1 i)))])))])))))

(define-for-syntax prim-table
  #'(;; Numbers
     [add1 #f #f add1v (z -> z)]
     [sub1 #f #f sub1v (z -> z)]
     [+    #f #f +v    (#:rest z -> z)]
     [-    #f #f -v    (#:rest z -> z)]
     [*    #f #f *v    (#:rest z -> z)]
     [=    #t #f =v    (#:rest z -> b)]
     [number? #f #f numberv? (any -> b)]
     [zero?   #t #f zero?v (z -> b)]
     ;; Comparisons
     [equal? #t #f equalv? (any any -> b)]
     [eqv? #t #f equalv? (any any -> b)]
     [eq? #t #f equalv? (any any -> b)]
     ;; Vectors
     [make-vector #f #t make-vectorv ((z -> v)
                                      (z any -> v))]
     [vector-ref #t #f vectorv-ref (v z -> any)]
     [vector-set! #f #t vectorv-set! (v z any -> !)]
     [vector-length #f #f vectorv-length (v -> z)]
     [vector? #f #f vectorv*? (any -> b)]
     ;; Strings
     [string? #f #f stringv? (any -> b)]
     ;; Symbols
     [symbol? #f #f symbolv? (any -> b)]
     ;; Procedures
     [procedure? #f #f procedurev? (any -> b)]
     ;; Imperative stuff
     [void? #f #f voidv? (any -> b)]
     [void #f #f voidv (-> !)]
     [error #f #f errorv (#:rest any -> any)]
     ;; Booleans
     [not #f #f notv (any -> b)]
     [boolean? #f #f booleanv? (any -> b)]
     ;; Pairs/lists
     [cons #f #t make-consv (any any -> p)]
     [list #f #t make-listv (#:rest any -> any)]
     [pair? #f #f consv*? (any -> b)]
     [null? #f #f nullv? (any -> b)]
     [set-car! #f #t set-car!v (p any -> !)]
     [set-cdr! #f #t set-cdr!v (p any -> !)]
     [car    #t #f carv    (p -> any)]
     [cdr    #t #f cdrv    (p -> any)]
     [caar   #t #f caarv   (p -> any)]
     [cadr   #t #f cadrv   (p -> any)]
     [cdar   #t #f cdarv   (p -> any)]
     [cddr   #t #f cddrv   (p -> any)]
     [caaar  #t #f caaarv  (p -> any)]
     [caadr  #t #f caadrv  (p -> any)]
     [cadar  #t #f cadarv  (p -> any)]
     [caddr  #t #f caddrv  (p -> any)]
     [cdaar  #t #f cdaarv  (p -> any)]
     [cdadr  #t #f cdadrv  (p -> any)]
     [cddar  #t #f cddarv  (p -> any)]
     [cdddr  #t #f cdddrv  (p -> any)]
     [caaaar #t #f caaaarv (p -> any)]
     [caaadr #t #f caaadrv (p -> any)]
     [caadar #t #f caadarv (p -> any)]
     [caaddr #t #f caaddrv (p -> any)]
     [cadaar #t #f cadaarv (p -> any)]
     [cadadr #t #f cadadrv (p -> any)]
     [caddar #t #f caddarv (p -> any)]
     [cadddr #t #f cadddrv (p -> any)]
     [cdaaar #t #f cdaaarv (p -> any)]
     [cdaadr #t #f cdaadrv (p -> any)]
     [cdadar #t #f cdadarv (p -> any)]
     [cdaddr #t #f cdaddrv (p -> any)]
     [cddaar #t #f cddaarv (p -> any)]
     [cddadr #t #f cddadrv (p -> any)]
     [cdddar #t #f cdddarv (p -> any)]
     [cddddr #t #f cddddrv (p -> any)]))

(mk-prims #:static primitive? changes-store? reads-store?)
