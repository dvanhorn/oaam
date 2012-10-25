#lang racket

(require "data.rkt" "notation.rkt" "do.rkt"
         (for-syntax syntax/parse racket/syntax
                     racket/match racket/list racket/base)
         (for-template racket/base racket/match)
         racket/stxparam
         racket/unsafe/ops)
(provide primitive? changes-store? reads-store? primitive? prim-constants
         mk-prims snull hash->kind
         yield force getter widen delay)

(define-syntax-parameter getter #f)
(define-syntax-parameter force #f)
(define-syntax-parameter widen #f)
(define-syntax-parameter delay #f)
(define-syntax-parameter yield
  (λ (stx)
     (raise-syntax-error #f "Must be within the context of a generator" stx)))

(define snull (set '()))

;; Classify different hash literals
(define (hash->kind h)
  (cond [(immutable? h)
         (cond [(hash-equal? h) 'immutable-equal]
               [(hash-eqv? h) 'immutable-eqv]
               [(hash-eq? h) 'immutable-eq])]
        [else
         (cond [(hash-equal? h) 'mutable-equal]
               [(hash-eqv? h) 'mutable-eqv]
               [(hash-eq? h) 'mutable-eq])]))
(define (immutable-hash? h)
  (case (hashv-kind h) [(immutable-equal immutable-eqv immutable-eq) #t] [else #f]))

;; Combinatorial combination of arguments
(define (toSetOfLists list-of-sets)
  (match list-of-sets
    ['() snull]
    [(cons hdS tail)
     (for*/set ([hd (in-set hdS)]
                [restlist (in-set (toSetOfLists tail))])
       (cons hd restlist))]))

(define-syntax-rule (νlits set-name lits ...)
  (begin (define lits #f) ...
         (begin-for-syntax
          (define-literal-set set-name
            (lits ...)))))
 ;; Identifiers for the crappy type DSL
 ;; Meanings (respectively): Number String Pair Null Boolean Vector Hash Symbol Char Any Void
(νlits type-abbrevs
       z fx s p v h y c any !
       ip op ;; input-port output-port
       ;; aliases
       b prt lst)
(begin-for-syntax
 (define-literal-set type-names (true false eof null))
 (struct type-union (abbrevs))
 (define (flatten-type tu)
   (match
       (let loop ([tu tu])
         (match tu
           [(? list? ts)
            (type-union
             (remove-duplicates
              (append-map (compose type-union-abbrevs loop) ts)))]
           [(type-union ts) tu] ;; guaranteed flat
           [(? symbol? s) (type-union (list s))]
           [_ (error 'flatten-type "Bad input ~a" tu)]))
     ;; Special case: singleton union.
     [(type-union (list single)) single]
     [tu tu]))
 (define (unalias t)
   (case t
     [(b) (type-union '(#t #f))]
     [(lst) (type-union '(p null))]
     [(prt) (type-union '(ip op))]
     [else t]))
 (define type-abbrevs?
   (let ([ta (literal-set->predicate type-abbrevs)]
         [tn (literal-set->predicate type-names)])
     (λ (x) (or (ta x) (tn x)))))
 (define (type->pred-stx t v)
   (with-syntax ([v v])
     (define (flat-pred t)
       (case t
         [(z) #'(or (number? v) (eq? v 'number))]
         [(fx) #'(or (fixnum? v) (eq? v 'number))]
         [(s) #'(or (string? v) (eq? v 'string))]
         [(y) #'(or (symbol? v) (eq? v 'symbol))]
         [(c) #'(or (char? v) (eq? v 'char))]
         [(v) #'(or (vectorv? v) (vectorv^? v))]
         [(p) #'(consv? v)]
         [(ip) #'(or (input-port? v) (input-port^? v))]
         [(op) #'(or (output-port? v) (output-port^? v))]
         [(h) #'(hashv? v)]
         ;; singleton types
         [(!) #'(void? v)]
         [(null) #'(eq? v '())]
         [(eof) #'(eof-object? v)]
         [(true) #'(eq? v #t)]
         [(false) #'(eq? v #f)]
         [else (error 'type->pred-stx "Not a predicate-able type ~a" t)]))
     (match t
       [(type-union (list-no-order #t #f)) #'(boolean? v)]
       [(type-union (list-no-order 'ip 'op))
        #`(or (port? v) (input-port^? v) (output-port^? v))]
       [(type-union others)
        #`(or #,@(map flat-pred others))]
       [_ (flat-pred t)])))

 (define (type-match t tmσ addr)
   #`(let ([addr #,addr])
       (let-syntax ([good
                     (syntax-rules ()
                       [(_ v pred)
                        (for/set ([v (in-set (getter #,tmσ addr))]
                                  #:when pred)
                          v)])])
         #,(if (eq? t 'any)
               #`(delay #,tmσ addr)
               #`(good v #,(type->pred-stx t #'v))))))
 (define (mk-is-abs? t)
   (cond [(type-union? t)
          (define each (map mk-is-abs? (type-union-abbrevs t)))
          (λ (arg-stx) #`(or #,@(for/list ([f (in-list each)]) (f arg-stx))))]
         [else
          (case t
            [(z fx) (λ (arg-stx) #`(eq? 'number #,arg-stx))]
            [(s) (λ (arg-stx) #`(eq? 'string #,arg-stx))]
            [(y) (λ (arg-stx) #`(eq? 'symbol #,arg-stx))]
            [(c) (λ (arg-stx) #`(eq? 'char #,arg-stx))]
            [else (λ (arg-stx) #'#f)])]))
 (define (abs-of t)
   (case t
     [(z fx) #''number]
     [(s) #''string]
     [(y) #''symbol]
     [(c) #''char]
     ;; singleton types only necessary to simplify mk-mk-simple
     [(true #t) #'#t]
     [(false #f) #'#f]
     [(n) #''()]
     [(!) #'(void)]
     [(e) #'eof]
     [else (error 'abs-of "Unsupported abs-of ~a" t)]))
 (define (mk-abs-out t)
   (cond [(type-union? t)
          (λ (σ-stx)
             #`(do (#,σ-stx)
                   ([a (in-list (list #,@(map abs-of (type-union-abbrevs t))))])
                 (yield a)))]
         [else (λ _ #`(yield #,(abs-of t)))]))

 (define (mk-checker no-σ? ts rest)
   (define mk-vs
     (for/list ([t (in-list ts)]
                [i (in-naturals)])
       (type-match t #'σderp #`(list-ref vs #,i))))
   (define mk-rest
     (and rest
          #`(for/list ([v (in-list (drop vs #,(length ts)))])
              #,(type-match rest #'σderp #'v))))
   (λ (prim)
      (with-syntax ([prim prim])
        #`(λ (#,@(if no-σ? #'() #'(σderp)) vs)
             (cond [#,(if rest
                          #`(>= (length vs) #,(length ts))
                          #`(= (length vs) #,(length ts)))
                    (define argsets #,(if rest
                                          #`(list* #,@mk-vs #,mk-rest)
                                          #`(list #,@mk-vs)))
                    (for ([a (in-list argsets)]
                          [i (in-naturals)]
                          #:when (null? a))
                      (log-info "Bad input to primitive: ~a (arg ~a)" 'prim i))
                    (toSetOfLists argsets)]
                   [else ∅])))))

 ;; Creates a transformer that expects pσ vs (so it can use yield-both or force if it needs to)
 ;; vs will have already been forced if necessary. Any types will have to be forced for non-abstract applications.
 (define ((mk-mk-simple mandatory mtypes op-rest return-out return-abs?) primitive widen?)
   (define arglist (generate-temporaries (map (λ _ #'v) mandatory)))
   (with-syntax* ([((rest ...) (ap ...))
                   (if op-rest #'((rest) (#%app apply)) #'(() (#%app)))]
                  [(args ...) arglist]
                  [guard
                   #`(or #,@(for/list ([m (in-list mandatory)]
                                       [arg (in-list arglist)])
                              (m arg))
                         #,@(listy (and op-rest
                                        #`(for/or ([v (in-list rest ...)])
                                            #,(op-rest #'v)))))]
                  [wrap (if widen? #'widen #'values)]
                  [op primitive])
     (define nullary? (and (not op-rest) (null? arglist)))
     ;; mk-simple
     (λ (stx)
        (syntax-parse stx
          [(pσ vs)
           (cond
            [nullary? #`(yield (wrap (op)))]
            [else
             (with-syntax ([(force-clauses ...)
                            (for/list ([t (in-list mtypes)]
                                       [arg (in-list arglist)]
                                       #:when (eq? t 'any))
                              #`[#,arg (force pσ #,arg)])])
               (quasisyntax/loc stx
                 (match vs
                   [(list-rest args ... rest ...)
                    (do (pσ) (force-clauses ...)
                      (cond [guard #,(return-out #'pσ)]
                            [else (yield (wrap (ap ... op args ... rest ...)))]))]
                   [_ (error 'mk-simple "Internal error ~a" vs)])))])]))))

 (define-syntax-class basic #:literals (∪)
   #:attributes (type is-abs? abs-out)
   (pattern name:id
            #:fail-unless (type-abbrevs? #'name) "Expected type abbreviation"
            #:attr type (unalias (syntax-e #'name))
            #:attr is-abs? (mk-is-abs? (attribute type))
            #:attr abs-out (mk-abs-out (attribute type)))
   (pattern (∪ b:basic ...)
            #:attr type (flatten-type (attribute b.type))
            #:attr is-abs? (mk-is-abs? (attribute type))
            #:attr abs-out (mk-abs-out (attribute type))))

 (define-syntax-class (flat no-σ?) #:literals (->)
   #:attributes (checker-fn mk-simple)
   (pattern (ts:basic ... (~optional (~seq #:rest r:basic)) -> t:basic)
            #:attr checker-fn (mk-checker no-σ? (attribute ts.type) (attribute r.type))
            #:attr mk-simple (mk-mk-simple (attribute ts.is-abs?)
                                           (attribute ts.type)
                                           (attribute r.is-abs?)
                                           (attribute t.abs-out)
                                           (attribute t.is-abs?))))
 (define-syntax-class (type no-σ?)
   #:attributes (checker-fn mk-simple)
   (pattern (~var f (flat no-σ?))
            #:attr checker-fn (attribute f.checker-fn)
            #:attr mk-simple (attribute f.mk-simple))
   (pattern ((~var fs (flat no-σ?)) ...)
            #:do [(define σs (if no-σ? #'() #'(σherderp)))]
            #:attr checker-fn
            #`(λ (#,@σs vs)
                 (or #,@(for/list ([f (in-list (attribute fs.checker-fn))])
                          #`(#,f #,@σs vs))))
            #:attr mk-simple
            (λ (widen?) (error 'mk-primitive-meaning "Simple primitives cannot have many arities."))))

 (define-syntax-class (prim-entry no-σ?)
   #:attributes (prim read-store? write-store? meaning checker-fn)
   (pattern [prim:id
             (~or 
              (~seq #:predicate p:basic (~bind [read-store? #'#t] [write-store? #'#f]))
              (~seq 
               (~or (~and #:simple (~bind [read-store? #'#t] [write-store? #'#f]))                          
                    (~seq read-store?:boolean write-store?:boolean implementation:id))
               (~var t (type no-σ?))
               (~optional (~and #:widen widen?))))]
            #:fail-when (and (attribute implementation) (attribute widen?))
            "Cannot specify that a simple implementation widens when giving an explicit implementation."
            #:attr checker-fn (or (let ([c (attribute t.checker-fn)])
                                    (and c (c #'prim)))
                                  ;; must be a predicate
                                  ((mk-checker no-σ? '(any) #f) #'prim))
            #:attr meaning (or (attribute implementation)
                               (and (attribute p)
                                    (syntax-parser
                                      [(pσ vs)
                                       #`(do (pσ) ([v (force pσ (car vs))])
                                           (yield #,(type->pred-stx (attribute p.type) #'v)))]))
                               ((attribute t.mk-simple) #'prim (syntax? (attribute widen?)))))))

(define-syntax (mk-static-primitive-functions stx)
  (syntax-parse stx
    [(_ primitive?:id changes-store?:id reads-store?:id
        ((~var p (prim-entry #f)) ...))
     (syntax/loc stx
       (begin (define (primitive? o)
                (case o [(p.prim) #t] ... [else #f]))
              (define (changes-store? o)
                (case o [(p.prim) p.write-store?] ...))
              (define (reads-store? o)
                (case o [(p.prim) p.write-store?] ...))))]))

(define-syntax (mk-primitive-meaning stx)
  (syntax-parse stx
    [(_ global-σ?:boolean mean:id defines ...
        ((~var p (prim-entry (syntax-e #'global-σ?))) ...))
     (define ((ap m) arg-stx)
       (if (procedure? m)
           (m arg-stx)
           (datum->syntax arg-stx (cons m arg-stx) arg-stx)))
     (quasisyntax/loc stx
       (begin
         defines ...
         (define-syntax-rule (mean o pσ l δ v-addrs)
           (case o
             #,@(for/list ([p (in-list (syntax->list #'(p.prim ...)))]
                           [w? (in-list (syntax->datum #'(p.write-store? ...)))]
                           [r? (in-list (syntax->datum #'(p.read-store? ...)))]
                           [m (in-list (map ap (attribute p.meaning)))]
                           [checker (in-list (attribute p.checker-fn))])
                  #`[(#,p)
                     ;; Checkers will force what they need to and keep the rest
                     ;; lazy. Forced values are exploded into possible
                     ;; argument combinations
                     (do (pσ) ([vs (#,checker
                                   #,@(if (syntax-e #'global-σ?) #'() #'(pσ))
                                   v-addrs)])
                       #,(cond [w? (m #'(pσ l δ vs))]
                               [r? (m #'(pσ vs))]
                               [else (m #'(vs))])
                         (continue))])))))]))

(define-simple-macro* (define/read (name:id rσ:id v:id ...) body ...+)
  ;; XXX: not capture-avoiding, so we have to be careful in our definitions
  (define-simple-macro* (name rσ vs)
    (match vs
      [(list v ...) body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

(define-simple-macro* (define/basic (name:id v:id ...) body ...+)
  (define-simple-macro* (name vs)
    (match vs
      [(list v ...) body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

(define-simple-macro* (define/write (name:id rσ:id l:id δ:id v:id ... [opv:id opval:expr] ...) body ...+)
  (define-simple-macro* (name rσ l δ vs)
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

;; XXX: Unfortunately needs σ
(define-simple-macro* (yield-both bσ)
  (do (bσ) ([b (in-list '(#t #f))]) (yield b)))

(define-syntax (mk-prims stx)
  (syntax-parse stx
    [(_ (~and #:static static?) primitive?:id changes-store?:id reads-store?:id)
     (quasisyntax/loc stx
       (mk-static-primitive-functions
        primitive? changes-store? reads-store? #,prim-table))]
    [(_ global-σ?:boolean mean:id clos?:id rlos?:id)
     (quasisyntax/loc stx
       (mk-primitive-meaning global-σ? mean #,@(prim-defines #'clos? #'rlos?) #,prim-table))]))

(define-for-syntax (prim-defines clos? rlos?)
  (with-syntax ([clos? clos?]
                [rlos? rlos?])
    #'((define-syntax-rule (yield-delay ydσ v)
         (do (ydσ) ([v* (delay ydσ v)]) (yield v*)))
       (define-simple-macro* (errorv vs) (continue))

       (define/basic (procedure?v v) (yield (or (clos? v) (rlos? v))))
       (define/basic (vectorv-length v)
         (match v
           [(or (vectorv len _) (vectorv^ len _)) (yield len)]))

       (define/basic (integer->charv z)
         (cond [(eq? z 'number) (yield 'char)]
               [(integer? z) (yield (widen (integer->char z)))]
               [else
                (log-info "integer->charv on non-integer")
                (continue)]))

       (define/basic (hashv-equal? h)
         (case (hashv-kind h) [(immutable-equal mutable-equal) #t] [else #f]))
       (define/basic (hashv-eqv? h)
         (case (hashv-kind h) [(immutable-eqv mutable-eqv) #t] [else #f]))
       (define/basic (hashv-eq? h)
         (case (hashv-kind h) [(immutable-eq mutable-eq) #t] [else #f]))
       ;; Not a general predicate. Only for immutable hashes, vectors, strings, byte-strings and boxes.
       ;; Currently we have only immutable hashes.
       (define/basic (immutablev? v)
         (match v
           [(? hashv? h) (yield (immutable-hash? h))]
           [_ (yield #f)]))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that read the store

       (define/read (equalv? eσ v0 v1)
         (define-syntax-rule (both-if pred) (if pred (yield-both eσ) (yield #f)))
         (do (eσ) ([v0 (force eσ v0)]
                   [v1 (force eσ v1)])
           (match* (v0 v1)
             [((? clos?) _) (both-if (clos? v1))] ;; FIXME: not right for concrete
             [(_ (? clos?)) (yield #f)] ;; first not a closure
             [((? consv?) _) (both-if (consv? v1))] ;; FIXME: not right for concrete
             [(_ (? consv?)) (yield #f)] ;; first not a cons
             [((? vectorv?) _) (both-if (vectorv? v1))] ;; FIXME: not right for concrete
             [(_ (? vectorv?)) (yield #f)] ;; first not a vector
             [((? primop?) _) (yield (equal? v0 v1))]
             [(_ (? primop?)) (yield #f)] ;; first not a primop
             [((? number?) _) (cond [(eq? 'number v1) (yield-both eσ)]
                                    [(number? v1) (yield (= v0 v1))]
                                    [else (yield #f)])]
             [('number _) (both-if (or (eq? 'number v1) (number? v1)))]
             [(_ 'number) (yield #f)]
             [((? string?) _) (cond [(eq? 'string v1) (yield-both eσ)]
                                    [(string? v1) (yield (string=? v0 v1))]
                                    [else (yield #f)])]
             [('string _) (both-if (or (eq? 'string v1) (string? v1)))]
             [(_ 'string) (yield #f)]
             [((? symbol?) _) (cond [(eq? 'symbol v1) (yield-both eσ)]
                                    [(symbol? v1) (yield (eq? v0 v1))]
                                    [else (yield #f)])]
             [('symbol _) (both-if (or (eq? 'symbol v1) (symbol? v1)))]
             [((? boolean?) _) (yield (equal? v0 v1))]
             [('() _) (yield (eq? '() v1))]
             [(_ '()) (yield #f)]
             [((? void?) _) (yield (void? v1))]
             [(_ (? void?)) (yield #f)]
             [(_ _) (error 'equalv? "Incomplete match ~a ~a" v0 v1)])))

       (define/read (vectorv-ref vrσ vec z)
         (match vec
           [(vectorv _ l)
            (cond [(eq? 'number z)
                   (error 'vectorv-ref "Abstract vectors should have a single cell")]
                  [(or (< z 0) (>= z (length l))) 
                   (log-info "vectorv-ref out of bounds")
                   (continue)]
                  [else (yield-delay vrσ (list-ref l z))])]
           [(vectorv^ _ abs-cell) (yield-delay vrσ abs-cell)]))

       (define/read (carv aσ p) (yield-delay aσ (consv-car p)))
       (define/read (cdrv dσ p) (yield-delay dσ (consv-cdr p)))

       (define/read (core-hashv-ref hσ h k)
         (error 'durp))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that write the store
       (define/write (vectorv-set! !σ l δ vec i val)
         (match vec
           [(vectorv _ addrs)
            (cond [(eq? 'number i)
                   (error 'vectorv-set! "Abstract vectors should have a single cell")]
                  [(or (< z 0) (>= z (length addrs)))
                   (log-info "vectorv-set! out out bounds")
                   (continue)]
                  [else (do (!σ) ([σ*-vec #:join !σ (list-ref addrs i) (force !σ val)])
                          (yield (void)))])]
           [(vectorv^ _ abs-cell)
            (do (!σ) ([σ*-vec^ #:join !σ abs-cell (force !σ val)])
              (yield (void)))]))

       (define-simple-macro* (prim-vectorv vσ l δ vs)
         (match (widen (length vs))
           ['number
            (define V-addr (make-var-contour `(V . ,l) δ))
            (do (vσ) loop ([v vs])
                (match v
                  ['() (yield (vectorv^ 'number V-addr))]
                  [(cons v vrest)
                   (do (vσ) ([σ*-pv^ #:join vσ V-addr (force vσ v)])
                     (loop σ*-pv^ vrest))]))]
           [size
            (do (vσ) loop ([v vs] [i 0] [addrs '()])
                (match v
                  ['() (yield (vectorv size (reverse addrs)))]
                  [(cons v vrest)
                   (define addr (make-var-contour `(V ,i . ,l) δ))
                   (do (vσ) ([σ*-pv #:join vσ addr (force vσ v)])
                     (loop σ*-pv vrest (add1 i) (cons addr addrs)))]))]))
       
       (define/write (make-vectorv vσ l δ size [default 0])
         (match (widen size)
           ['number
            (define V-addr (make-var-contour `(V . ,l) δ))
            (do (vσ) ([σ*-mv^ #:join vσ V-addr (force vσ default)])
              (yield (vectorv^ size V-addr)))]
           [_ (define V-addrs
                (for/list ([i (in-range size)]) (make-var-contour `(V ,i . ,l) δ)))
              (do (vσ) ([σ*-mv #:join* vσ V-addrs (make-list size (force vσ default))])
                (yield (vectorv size V-addrs)))]))

       (define/write (make-consv cσ l δ v0 v1)
         (define A-addr (make-var-contour `(A . ,l) δ))
         (define D-addr (make-var-contour `(D . ,l) δ))
         (do (cσ) ([σ*A #:join cσ A-addr (force cσ v0)]
                  [σ*D #:join σ*A D-addr (force σ*A v1)])
           (yield (consv A-addr D-addr))))

       (define/write (set-car!v aσ l δ p v)
         (do (aσ) ([σ*a! #:join aσ (consv-car p) (force aσ v)]) (yield (void))))
       (define/write (set-cdr!v dσ l δ p v)
         (do (dσ) ([σ*d! #:join dσ (consv-cdr p) (force dσ v)]) (yield (void))))

       (define/write (hashv-set hσ l δ h k v)
         (cond [(immutable-hash? h)
                (define P-addr (make-var-contour `(P . ,l) δ))
                (define K-addr (make-var-contour `(K . ,l) δ))
                (define V-addr (make-var-contour `(V . ,l) δ))
                (do (hσ) ([σ*P #:join hσ P-addr (set h)]
                         [σ*K #:join σ*P K-addr (force σ*P k)]
                         [σ*V #:join σ*K V-addr (force σ*K v)])
                  (yield (hash-with (hashv-kind h) P-addr K-addr V-addr)))]
               [(hash? h) (error 'hashv-set "Fail gracefully from literal to abstract value ~a ~a ~a" h k v)]
               [else
                (log-info "hashv-set non-hash")
                (continue)]))

       (define/write (hashv-remove hσ l δ h k)
         (cond [(immutable-hash? h)
                (define P-addr (make-var-contour `(P . ,l) δ))
                (define K-addr (make-var-contour `(K . ,l) δ))
                (do (hσ) ([σ*P #:join hσ P-addr (set h)]
                         [σ*K #:join σ*P K-addr (force σ*P k)])
                  (yield (hash-without (hashv-kind h) P-addr K-addr)))]
               [(hash? h) (error 'hashv-remove "Fail gracefully from literal to abstract value ~a ~a ~a" h k v)]
               [else
                (log-info "hashv-remove non-hash")
                (continue)]))

       (define/write (hashv-set! h!σ l δ h k v) (error 'TODO-hash-set!))
       (define/write (hashv-remove! h!σ l δ h k v) (error 'TODO-hash-remove!))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; I/O
       (define-simple-macro* (mk-port-open name port^ open-port)
         (define/write (name ioσ l δ s)
           (match (widen s)
             ['string
              (define status-addr (make-var-contour `(Port . ,l) δ))
              (do (ioσ) ([openσ #:join ioσ status-addr (set 'open)])
                (yield (port^ status-addr)))]
             [s (yield (open-port s))])))
       (mk-port-open open-input-filev input-port^ open-input-file)
       (mk-port-open open-output-filev output-port^ open-output-file)

       (define-simple-macro* (mk-port-close name port^ close-port)
         (define/write (name ioσ l δ ip)
           (match ip
             [(port^ status)
              (do (ioσ) ([closeσ #:join ioσ status (set 'closed)])
                (yield (void)))]
             [ip (close-port ip)
                 (yield (void))])))
       (mk-port-close close-input-portv input-port^ close-input-port)
       (mk-port-close close-output-portv output-port^ close-output-port)

       (define/read (port-closed?v ioσ prt)
         (match prt
           [(or (input-port^ status-addr) (output-port^ status-addr))
            (do (ioσ) ([status (getter ioσ status-addr)])
              (yield (eq? status 'closed)))]
           [real-port (yield (port-closed? real-port))]))
       ;; FIXME: optional argument version should be in add-lib
       (define/read (writev ioσ any op)
         (match op
           [(output-port^ status-addr)
            (do (ioσ) ([status (getter ioσ status-addr)])
              (case status
                [(open) (yield (void))]
                [(closed) (continue)]
                [else (error 'writev "Bad port status ~a" status)]))]
           [real-port
            (cond [(port-closed? real-port) (continue)]
                  [else
                   (do (ioσ) loop ([vs (set->list (force ioσ any))])
                       (match vs
                         ['() (yield (void))]
                         [(cons v vs)
                          (write v real-port)
                          (loop ioσ vs)]
                         [_ (error 'writev "What. ~a" vs)]))])]))

       ;; FIXME: WHAT DO?
       (define/basic (readv ip) (yield '()))

       (define/read (newlinev ioσ op)
         (match op
           [(output-port^ status-addr)
            (do (ioσ) ([status (getter ioσ status-addr)])
              (case status
                [(open) (yield (void))]
                [(closed) (continue)]
                [else (error 'newlinev "Bad port status ~a" status)]))]
           [real-port
            (cond [(port-closed? real-port) (continue)]
                  [else (newline op)
                        (yield (void))])]))
       ;; FIXME: remove for time-apply
       (define/basic (timev any) (yield any)))))

(define-for-syntax prim-table
  #'(;; Numbers
     [add1 #:simple (z -> z) #:widen]
     [sub1 #:simple (z -> z) #:widen]
     [+    #:simple (#:rest z -> z) #:widen]
     [-    #:simple (#:rest z -> z) #:widen]
     [*    #:simple (#:rest z -> z) #:widen]
     [=    #:simple (z #:rest z -> b)]
     [<    #:simple (z #:rest z -> b)]
     [>    #:simple (z #:rest z -> b)]
     [<=    #:simple (z #:rest z -> b)]
     [>=    #:simple (z #:rest z -> b)]
     [unsafe-fx= #:simple (fx fx -> b)]
     [unsafe-fx< #:simple (fx fx -> b)]
     [unsafe-fx> #:simple (fx fx -> b)]
     [unsafe-fx<= #:simple (fx fx -> b)]
     [unsafe-fx>= #:simple (fx fx -> b)]
     [unsafe-fx- #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fx+ #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fx* #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxquotient #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxremainder #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxmodulo #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxabs #:simple (fx fx -> fx)] ;; XXX: could crash?
     [unsafe-fxmin #:simple (fx fx -> fx)]
     [unsafe-fxmax #:simple (fx fx -> fx)]
     [unsafe-fxand #:simple (fx fx -> fx) #:widen]
     [unsafe-fxxor #:simple (fx fx -> fx) #:widen]
     [unsafe-fxior #:simple (fx fx -> fx) #:widen]
     [unsafe-fxnot #:simple (fx -> fx) #:widen]
     [unsafe-fxlshift #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxrshift #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [number? #:predicate z]
     [zero? #:simple (z -> b)]
     ;; Generic Comparisons
     [equal? #t #f equalv? (any any -> b)]
     [eqv? #t #f equalv? (any any -> b)]
     [eq? #t #f equalv? (any any -> b)]
     ;; Vectors
     [vector #f #t prim-vectorv (#:rest any -> v)]
     [make-vector #f #t make-vectorv ((z -> v)
                                      (z any -> v))]
     [vector-ref #t #f vectorv-ref (v z -> any)]
     [vector-set! #f #t vectorv-set! (v z any -> !)]
     [vector-length #f #f vectorv-length (v -> z)]
     [vector? #:predicate v]
     ;; Strings
     [string? #:predicate s]
     [string->symbol #:simple (s -> y)]
     [string=? #:simple (s #:rest s -> b)]
     [string>? #:simple (s #:rest s -> b)]
     [string<? #:simple (s #:rest s -> b)]
     [string>=? #:simple (s #:rest s -> b)]
     [string<=? #:simple (s #:rest s -> b)]
     [string-ci=? #:simple (s #:rest s -> b)]
     [string-ci>? #:simple (s #:rest s -> b)]
     [string-ci<? #:simple (s #:rest s -> b)]
     [string-ci>=? #:simple (s #:rest s -> b)]
     [string-ci<=? #:simple (s #:rest s -> b)]
     [string-append #:simple (#:rest s -> s) #:widen]
     [number->string #:simple (z -> (∪ s false)) #:widen]
     ;; Characters
     [char? #:predicate c]
     [char=? #:simple (c #:rest c -> b)]
     [char<? #:simple (c #:rest c -> b)]
     [char>? #:simple (c #:rest c -> b)]
     [char>=? #:simple (c #:rest c -> b)]
     [char<=? #:simple (c #:rest c -> b)]
     [char-ci=? #:simple (c #:rest c -> b)]
     [char-ci<? #:simple (c #:rest c -> b)]
     [char-ci>? #:simple (c #:rest c -> b)]
     [char-ci>=? #:simple (c #:rest c -> b)]
     [char-ci<=? #:simple (c #:rest c -> b)]
     [char-alphabetic? #:simple (c -> b)]
     [char-numeric? #:simple (c -> b)]
     [char-whitespace? #:simple (c -> b)]
     [char-lower-case? #:simple (c -> b)]
     [char-upper-case? #:simple (c -> b)]
     [char->integer #:simple (c -> z) #:widen]
     [integer->char #:simple (z -> c) #:widen]
     [char-upcase #:simple (c -> c) #:widen]
     [char-downcase #:simple (c -> c) #:widen]
     ;; Symbols
     [symbol? #:predicate y]
     [symbol->string #:simple (y -> s)]
     ;; Procedures
     [procedure? #f #f procedure?v (any -> b)]
     ;; Imperative stuff
     [void? #:predicate !]
     [void #:simple (-> !)]
     [error #f #f errorv (#:rest any -> any)]
     ;; Booleans
     [not #:predicate false]
     [boolean? #:predicate b]
     ;; Pairs/lists
     [cons #f #t make-consv (any any -> p)]
     [pair? #:predicate p]
     [null? #:predicate null]
     [set-car! #f #t set-car!v (p any -> !)]
     [set-cdr! #f #t set-cdr!v (p any -> !)]
     [car    #t #f carv    (p -> any)]
     [cdr    #t #f cdrv    (p -> any)]
     ;; Ports
     [input-port? #:predicate ip]
     [output-port? #:predicate op]
     [open-input-file #f #t open-input-filev (s -> ip)]
     [open-output-file #f #t open-output-filev (s -> op)]
     [close-input-port #f #t close-input-portv (ip -> !)]
     [close-output-port #f #t close-output-portv (op -> !)]
     [port-closed? #t #f port-closed?v (prt -> b)]
#;#;
     [current-input-port #f #f current-input-portv (-> ip)]
     [current-output-port #f #f current-input-portv (-> op)]
     [read #f #f readv ((-> lst) ;; XXX: impoverished read
                        (ip -> lst))]
     [write #t #f writev ((any -> !)
                          (any op -> !))]
     [newline #t #f newlinev ((-> !)
                              (op -> !))]
     [eof-object? #:predicate eof]
     ;; time should be with time-apply, but that means supporting apply...
     [time #f #f timev (any -> any)]
     ;; Hashes
     [hash-equal?   #f #f hashv-equal?     (h -> b)]
     [hash-eqv?     #f #f hashv-eqv?       (h -> b)]
     [hash-eq?      #f #f hashv-eq?        (h -> b)]
     [hash-set      #f #t hashv-set        (h any any -> h)]
     [hash-remove   #f #t hashv-remove     (h any -> h)]
#;#;#;#;#;#;#;
     [core-hash-ref #t #f hashv-ref        (h any -> any)]
     [hash-has-key? #t #f hashv-has-key?   (h any -> b)]
     [hash-set!     #f #t hashv-set!       (h any any -> !)]
     [hash-remove!  #f #t hashv-remove!    (h any -> !)]
     [make-hash     #f #t make-hashv-equal ((-> h)
                                            (lst -> h))]
     [make-hasheqv  #f #t make-hashv-eqv   ((-> h)
                                            (lst -> h))]
     [make-hasheq   #f #t make-hashv-eq    ((-> h)
                                            (lst -> h))]
     [immutable?    #f #f immutablev?      (any -> b)]))

(mk-prims #:static primitive? changes-store? reads-store?)

(define prim-constants
  (hasheq 'eof eof
          'null '()
          'true #t
          'false #f))