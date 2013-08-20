#lang racket

(require "data.rkt" "notation.rkt" "do.rkt"
         (for-syntax syntax/parse racket/syntax
                     racket/match racket/list racket/base)
         (for-meta 2 racket/base)
         racket/stxparam)
(provide getter μgetter force widen delay yield yield-meaning snull         
         mk-primitive-meaning mk-static-primitive-functions
         (for-syntax if-μ))

(define-syntax-parameter getter #f)
(define-syntax-parameter μgetter #f)
(define-syntax-parameter force #f)
(define-syntax-parameter widen #f)
(define-syntax-parameter delay #f)
(begin-for-syntax
 (define-syntax (if-μ stx)
   (syntax-case stx ()
     [(_ t) #'(if (syntax-parameter-value #'abs-count?)
                  (list t)
                  '())]
     [(_ t e) #'(if (syntax-parameter-value #'abs-count?)
                    t
                    e)])))

(define-syntax-parameter yield
  (λ (stx)
     (raise-syntax-error #f "Must be within the context of a generator" stx)))
;; Yield is an overloaded term that will do some manipulation to its
;; input. Yield-meaning is the intended meaning of yield.
(define-syntax-parameter yield-meaning
  (λ (stx) (raise-syntax-error #f "Must parameterize for mk-analysis" stx)))

(define snull (singleton '()))

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
         (provide lits ...)
         (begin-for-syntax
          (define-literal-set set-name
            (lits ...)))))
 ;; Identifiers for the crappy type DSL
(νlits type-abbrevs
       n ;; Number (Complex)
       z ;; Integer
       q ;; Rational
       fx ;; Fixnum (Concrete only)
       fl ;; Flonum
       s ;; String
       p ;; Pair
       v ;; Vector
       h ;; Hash
       y ;; Symbol
       c ;; Char
       any
       ! ;; Void
       ip op ;; input-port output-port
       ;; aliases
       b prt lst r)
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
     [(r) (type-union '(q fl))]
     [else t]))
 (define type-abbrevs?
   (let ([ta (literal-set->predicate type-abbrevs)]
         [tn (literal-set->predicate type-names)])
     (λ (x) (or (ta x) (tn x)))))
 (define (type->pred-stx t v)
   (with-syntax ([v v])
     (define (flat-pred t)
       (case t
         [(n) #'(or (number? v) (number^? v))]
         [(z) #'(or (integer? v) (number^? v))]
         [(q) #'(or (rational? v) (number^? v))]
         [(fx) #'(or (fixnum? v) (number^? v))]
         [(fl) #'(or (flonum? v) (number^? v))]
         [(s) #'(or (string? v) (string^? v))]
         [(y) #'(or (symbol? v) (symbol^? v))]
         [(c) #'(or (char? v) (char^? v))]
         [(v) #'(or (vectorv-immutable? v)
                    (eq? v vec0)
                    ;; real immutable vector
                    (and (immutable? v) (vector? v))
                    (vectorv^? v)
                    (qvector^? v)
                    (vectorv-immutable^? v)
                    ;; black hole vectors
                    (vector^? v)
                    (vector-immutable^? v))]
         [(p) #'(or (consv? v) (cons^? v) (qcons^? v))]
         [(ip) #'(or (input-port? v) (input-port^? v) (and (eq? v ●) ●))]
         [(op) #'(or (output-port? v) (output-port^? v) (and (eq? v ●) ●))]
         [(h) #'(hashv? v)]
         ;; singleton types
         [(!) #'(or (void? v) (and (eq? v ●) ●))]
         [(null ()) #'(or (eq? v '()) (and (eq? v ●) ●))]
         [(eof) #'(or (eof-object? v) (and (eq? v ●) ●))]
         [(true #t) #'(or (eq? v #t) (and (eq? v ●) ●))]
         [(false #f) #'(or (eq? v #f) (and (eq? v ●) ●))]
         [else (error 'type->pred-stx "Not a predicate-able type ~a" t)]))
     (match t
       [(type-union (list-no-order #t #f)) #'(boolean? v)]
       [(type-union (list-no-order 'ip 'op))
        #`(or (port? v) (input-port^? v) (output-port^? v))]
       [(type-union others)
        #`(or #,@(map flat-pred others))]
       [_ (flat-pred t)])))

;; FIXME: does not carry actions correctly
 (define (type-match t addr)
   #`(let ([addr #,addr])
       (let-syntax ([good
                     (syntax-rules ()
                       [(_ v pred)
                        (for/set ([v (in-set (getter addr))] ;; uses target-σ
                                  #:when pred)
                          v)])])
         #,(if (eq? t 'any)
               #`(delay addr) ;; uses target-σ
               #`(good v #,(type->pred-stx t #'v))))))

 (define (mk-is-abs? t)
   (cond [(type-union? t)
          (define each (map mk-is-abs? (type-union-abbrevs t)))
          (λ (arg-stx) #`(or #,@(for/list ([f (in-list each)]) (f arg-stx))))]
         [else
          (case t
            [(n q z fx fl) (λ (arg-stx) #`(number^? #,arg-stx))]
            [(s) (λ (arg-stx) #`(string^? #,arg-stx))]
            [(y) (λ (arg-stx) #`(symbol^? #,arg-stx))]
            [(c) (λ (arg-stx) #`(char^? #,arg-stx))]
            [(p) (λ (arg-stx) #`(or (cons^? #,arg-stx)
                                    (qcons^? #,arg-stx)))]
            [(v) (λ (arg-stx) #`(or (vector^? #,arg-stx)
                                    (qvector^? #,arg-stx)
                                    (eq? vector-immutable^ #,arg-stx)))]
            [else (λ (arg-stx) #'#f)])]))

 (define (abs-of t stx)
   (case t
     [(n z fx fl q) #'number^]
     [(s) #'string^]
     [(y) #'symbol^]
     [(c) #'char^]
     ;; singleton types only necessary to simplify mk-mk-simple
     [(true #t) #'#t]
     [(false #f) #'#f]
     [(n) #''()]
     [(!) #'(void)]
     [(e) #'eof]
     [else #'(raise-syntax-error #f (format "Unsupported abs-of ~a" #,t) #,stx)]))

;; TODO remove λ
 (define (mk-abs-out t stx)
   (cond [(type-union? t)
          #`(do ([a (in-list (list #,@(for/list ([t (in-list (type-union-abbrevs t))]) (abs-of t stx))))])
                (yield a))]
         [else #`(yield #,(abs-of t stx))]))

;; Doesn't yield, so doesn't need μ or τ
 (define (mk-checker no-σ? ts rest)
   (define mk-vs
     (for/list ([t (in-list ts)]
                [i (in-naturals)])
       (type-match t #`(list-ref vs #,i))))
   (define mk-rest
     (and rest
          #`(for/list ([v (in-list (drop vs #,(length ts)))])
              #,(type-match rest #'v))))
   (λ (prim mult-ary?)
      (with-syntax ([prim prim])
        #`(λ (#,@(if no-σ? #'() #'(σderp)) vs)
             (syntax-parameterize ([target-σ (make-rename-transformer #'σderp)])
               (cond [#,(if rest
                            #`(>= (length vs) #,(length ts))
                            #`(= (length vs) #,(length ts)))
                      (define argsets #,(if rest
                                            #`(list* #,@mk-vs #,mk-rest)
                                            #`(list #,@mk-vs)))
                      #,@(listy (and (not mult-ary?)
                                     #'(for ([a (in-list argsets)]
                                             [i (in-naturals)]
                                             #:when (null? a))
                                         (log-info "Bad input to primitive: ~a (arg ~a)" 'prim i))))
                      (toSetOfLists argsets)]
                     [else
                      #,@(listy
                          (and (not mult-ary?)
                               #`(log-info "Primitive application arity mismatch (Expect: ~a, given ~a): ~a"
                                           #,(length ts) (length vs) 'prim)))
                      ∅]))))))

 ;; Creates a transformer that expects pσ vs (so it can use yield-both or force if it needs to)
 ;; vs will have already been forced if necessary. Any types will have to be forced for non-abstract applications.
 (define ((mk-mk-simple mandatory mtypes op-rest return-out return-abs?) primitive widen?)
   (define arglist (generate-temporaries (map (λ _ #'v) mandatory)))
   (with-syntax* ([((rest ...) rest-arg (ap ...))
                   (if op-rest
                       #'((rest) rest (#%app apply))
                       #'(() '() (#%app)))]
                  [(args ...) arglist]
                  [return-out return-out]
                  [guard
                   #`(or #,@(for/list ([m (in-list mandatory)]
                                       [arg (in-list arglist)])
                              (m arg))
                         #,@(listy (and op-rest
                                        #`(for/or ([v (in-list rest ...)])
                                            #,(op-rest #'v)))))]
                  [wrap (if widen? #'widen #'values)]
                  [op primitive])
     ;; mk-simple
     (λ (stx)
        (syntax-parse stx
          [(vs)
            (with-syntax ([(force-clauses ...)
                            (for/list ([t (in-list mtypes)]
                                       [arg (in-list arglist)]
                                       #:when (eq? t 'any))
                              #`[#,arg #:in-force #,arg])])
               (quasisyntax/loc stx
                 (match vs
                   [(list-rest args ... rest-arg)
                    (do (force-clauses ...)
                      (cond [guard return-out]
                            [else (yield (wrap (ap ... op args ... rest ...)))]))]
                   [_ (error 'mk-simple "Internal error ~a" vs)])))]))))

 (define-syntax-class basic #:literals (∪)
   #:attributes (type is-abs? abs-out)
   (pattern name:id
            #:fail-unless (type-abbrevs? #'name) "Expected type abbreviation"
            #:attr type (unalias (syntax-e #'name))
            #:attr is-abs? (mk-is-abs? (attribute type))
            #:attr abs-out (mk-abs-out (attribute type) #'name))
   (pattern (~and stx
                  (∪ b:basic ...))
            #:attr type (flatten-type (attribute b.type))
            #:attr is-abs? (mk-is-abs? (attribute type))
            #:attr abs-out (mk-abs-out (attribute type) #'stx)))

 (define-syntax-class (flat no-σ?) #:literals (->)
   #:attributes (checker-fn mk-simple (ts 1))
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
            #:attr checker-fn ;; doesn't yield, so doesn't need τ or μ
            (λ (prim _)
               ;; Abstract over some bits.
               #`(λ (#,@σs vs)
                    (syntax-parameterize ([target-σ (make-rename-transformer #'σherderp)])
                      (or #,@(for/list ([f (in-list (attribute fs.checker-fn))])
                               #`(let ([arg (#,(f prim #t) #,@σs vs)])
                                   (and (not (∅? arg)) arg)))
                          (begin (log-info "Primitive application arity mismatch (Expect: ~a, given ~a): ~a"
                                           '#,(map length (attribute fs.ts)) (length vs) 'prim)
                                 ∅)))))
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
                                    (and c (c #'prim #f)))
                                  ;; must be a predicate
                                  ((mk-checker no-σ? '(any) #f) #'prim #f))
            #:attr meaning (or (attribute implementation)
                               (and (attribute p)
                                    (syntax-parser
                                      [(vs)
                                       #`(do ([v #:in-force (car vs)]
                                              [res (in-list
                                                    (let ([r #,(type->pred-stx (attribute p.type) #'v)])
                                                      (if (eq? v ●)
                                                          '(#t #f)
                                                          (list r))))])
                                             (yield res))]))
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
         [(_ gb?:boolean σpb?:boolean 0b?:boolean
             mean:id compile:id co:id defines ... ((~var p (prim-entry (syntax-e #'gb?))) ...))
          (define global-σ? (syntax-e #'gb?))
          (define σ-passing? (syntax-e #'σpb?))
          (define σ-∆sv? (syntax-parameter-value #'σ-∆s?))
          (define compiledv? (syntax-parameter-value #'compiled?))
          (define μ? (syntax-parameter-value #'abs-count?))
          (define 0cfa? (syntax-e #'0b?))          
          (define ((ap m) arg-stx)
            (if (procedure? m)
                (m arg-stx)
                (datum->syntax arg-stx (cons m arg-stx) arg-stx)))
          (define hidden-σ (and σ-∆sv? (not global-σ?) (generate-temporary #'hidden)))
          (with-syntax ([((μ-op ...) (target-μ-op ...))
                         (if (or global-σ? (not μ?))
                             #'(() ())
                             #'((pμ) (target-μ)))]
                        [((σ-gop ...) (target-σ-op ...))
                         (if σ-passing?
                             #'((pσ) (target-σ))
                             #'(() ()))]
                        [(top ...) (listy hidden-σ)]
                        [topp (or hidden-σ #'pσ)]
                        [(top-op ...) (if (and σ-∆sv? (not global-σ?)) #'(top-σ) #'())]
                        [(δ-op ...) (if 0cfa? #'() #'(δ))])
            (define eval
              #`(case o
                  #,@(for/list ([pid (in-list (syntax->list #'(p.prim ...)))]
                                [w? (in-list (syntax->datum #'(p.write-store? ...)))]
                                [r? (in-list (syntax->datum #'(p.read-store? ...)))]
                                [m (in-list (map ap (attribute p.meaning)))]
                                [checker (in-list (attribute p.checker-fn))])
                       #`[(#,pid)
                          (λP #,pid (ℓ δ k v-addrs)
                              (with-prim-yield
                               k
                               ;; Checkers will force what they need to and keep the rest
                               ;; lazy. Forced values are exploded into possible
                               ;; argument combinations
                               (do ([vs (#,checker target-σ-op ... v-addrs)])
                                 #,(cond [w? (m #'(ℓ δ vs))]
                                         [else #;r? (m #'(vs))]))))])))
            (quasisyntax/loc stx
              (begin
                ;; Let primitives yield single values instead of entire states.
                #,#'(define-syntax (with-prim-yield syn)
                      (syntax-parse syn
                        [(_ k body)
                         (define yield-tr (syntax-parameter-value #'yield-meaning))
                         (define new
                           (λ (sx)
                              (syntax-parse sx
                                [(_ v)
                                 (yield-tr (syntax/loc sx (yield (co k v))))])))
                         #`(syntax-parameterize ([yield #,new]) body)]))
                defines ...
                ;; λP very much like λ%
                (define-syntax-rule (... (λP f (ℓ δ k v-addrs) body ...))
                  #,(if compiledv?
                        #'(procedure-rename
                           (λ (top ... σ-gop ... μ-op ... pτ ℓ δ-op ... k v-addrs)
                              (syntax-parameterize ([top-σ (make-rename-transformer #'topp)]
                                                    [target-σ (make-rename-transformer #'pσ)]
                                                    [target-μ (make-rename-transformer #'pμ)]
                                                    [target-τ (make-rename-transformer #'pτ)])
                                body (... ...)))
                           'f)
                        #'(let () body (... ...))))
                ;; Identity if not compiled.
                (define-syntax-rule (compile o)
                  #,(if compiledv? eval #'o))
                (define-syntax-rule (mean o ℓ δ k v-addrs)
                  #,(if compiledv?
                        #'(o top-op ... target-σ-op ... target-μ-op ... target-τ ℓ δ-op ... k v-addrs)
                        eval)))))]))
