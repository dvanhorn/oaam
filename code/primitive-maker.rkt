#lang racket

(require "data.rkt" "notation.rkt" "do.rkt" "parameters.rkt"
         (for-syntax syntax/parse racket/syntax
                     (except-in racket/match match match*) racket/list (except-in racket/base and)
                     syntax/parse/experimental/template
                     racket/pretty
                     "notation.rkt")
         racket/unsafe/ops
         racket/stxparam)
(provide getter widen yield snull prim-extras alt-reverse
         mk-primitive-meaning mk-static-primitive-functions
         ;; for use only by primitives.rkt
         original-yield)

;; Extra hidden parameters prim-meaning might need.
(define-syntax-parameter prim-extras '())
;; General lookup and flat value widening
(define-syntax-parameter getter #f)
(define-syntax-parameter widen #f)
(define-syntax-parameter yield
  (λ (stx)
     (raise-syntax-error #f "Unset" stx)))
;; Internal use only for primitives that need to produce non-co states
(define-syntax-parameter original-yield #f)

(define (alt-reverse l)
  (let recur ([l l] [acc '()])
    (if (pair? l)
        (recur (unsafe-cdr l) (cons (unsafe-car l) acc))
        acc)))

(define snull (singleton '()))

;; Combinatorial combination of arguments
(define (toSetOfLists list-of-sets)
  (match list-of-sets
    ['() snull]
    [(cons hdS tail)
     (for*/set ([hd (in-set hdS)]
                [restlist (in-set (toSetOfLists tail))])
       (cons hd restlist))]))

(define (prim-bad-input prim arg val)
  (log-info "Bad input to primitive: ~a (arg ~a): ~a" prim arg val))

(define (prim-bad-rest prim arg val)
  (log-info "Bad input to primitive: ~a (rest arg ~a): ~a" prim arg val))

(define (prim-arity-error prim expected given)
  (log-info "Primitive application arity mismatch ~a: expect: ~a, given ~a"
            prim expected given))

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
       fn ;; Procedure
       any
       ! ;; Void
       ip op ;; input-port output-port
       ;; aliases
       b prt lst r)
(begin-for-syntax
 ;; Avoid code duplication by only generating one filter per "type"
 ;; we come across while generating definitions.
 (define type-checkers #f)
 (define-literal-set type-names (true false eof null))
 (struct type-arrow (in out) #:transparent)
 (struct type-rest-arrow (in rest out) #:transparent)
 (struct type-union (abbrevs) #:transparent)
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
 (define ((type->pred-stx clos? rlos? kont?) t v)
   (with-syntax ([v v]
                 [clos? clos?]
                 [rlos? rlos?]
                 [kont? kont?])
     (define (flat-pred t)
       (case t
         [(n) #'(or (number? v) (number^? v))]
         [(z) #'(or (integer? v) (number^? v))]
         [(q) #'(or (rational? v) (number^? v))]
         [(fx) #'(or (fixnum? v) (number^? v))]
         [(fl) #'(or (flonum? v) (number^? v))]
         [(fn) #'(or (clos? v) (rlos? v) (primop? v) (kont? v))]
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

;; "any" types don't get forced unless the implementation decides to.
;; this cuts down on the state fan-out problem.
;; If not any, get all values and filter out only the ones that match
;; the type.
;; If nothing matches, we have a stuck state, and possibly log an error.
 (define (type-match predfn t tmσ addr)
   (λ (acc on-err)
      (define body
        (cond
         [(eq? t 'any)
          #`(bind-delay (res #,tmσ addr)
                        (do-values (cons res #,acc)))]
         [else
          #`(bind-get (gres #,tmσ addr)
                      (let* ([filtered
                              (for/set ([v (in-set gres)] #:when #,(predfn t #'v)) v)]
                             [#,acc (cons filtered #,acc)])
                        #,@(if on-err
                               #`((when (∅? filtered)
                                    #,(on-err #'gres)))
                               #'())
                        (do-values #,acc)))]))
      #`(let ([addr #,addr]) #,body)))

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

 (define (abs-of t)
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
     [else (error 'abs-of "Unsupported abs-of ~a" t)]))

 (define (mk-abs-out t)
   (cond [(type-union? t)
          (λ (σ-stx)
             #`(do (#,σ-stx)
                   ([a (in-list (list #,@(map abs-of (type-union-abbrevs t))))])
                 (yield a)))]
         [else (λ _ #`(yield #,(abs-of t)))]))

 (define (mk-checker predfn ts rest)
   (define v-ids (generate-temporaries (make-list (length ts) #'v)))
   (define r-id (generate-temporary #'rest))
   (λ (mult-ary?)
      (define key (list ts rest mult-ary?))
      (cond
       ;; first is the name if it's there.
       [(hash-ref type-checkers key #f) => car]
       [else
        (with-syntax ([(vids ...) v-ids]
                      [rest-match (if rest r-id #''())])
          (define built
            (for/fold ([stx #`(do-values (toSetOfLists acc))])
                ([t (in-list ts)]
                 [v (in-list v-ids)]
                 [argnum (in-range (length ts) 0 -1)])
              (define tm (type-match predfn t #'σ v))
              #`(do-comp #:bind (#:σ σ acc)
                         #,(tm #'acc
                                 (and (not mult-ary?)
                                      (λ (tmp)
                                         #`(prim-bad-input prim #,argnum #,tmp))))
                         #,stx)))
          (define check-rest
            (and rest
                 (type-match predfn rest #'σ #'ra)))
          (define result
            (cons
             (generate-temporary #'checker-mk-checker)
             #`(tλ (#:σ σ prim apply? v-addrs)
                 (expect-do-values #:values 1
                   (match v-addrs
                     [(list-rest vids ... rest-match)
                      #,(if rest
                            #`(do (σ) loop ([raddrs #,r-id]
                                            [acc '()]
                                            [argnum #,(length ts)])
                                  (match raddrs
                                    ['() (let ([acc (alt-reverse acc)]) #,built)]
                                    [(cons ra rrest)
                                     (do-comp #:bind (#:σ σ acc)
                                              #,(check-rest #'acc
                                                            (and (not mult-ary?)
                                                                 (λ (tmp)
                                                                    #`(prim-bad-rest
                                                                       prim
                                                                       argnum
                                                                       #,tmp))))
                                              (loop σ rrest acc (add1 argnum)))]))
                            #`(let ([acc '()]) #,built))]
                     [vs #,@(listy
                             (and (not mult-ary?)
                                  #`(prim-arity-error prim #,(length ts) (length vs))))
                         (do-values ∅)])))))
          (hash-set! type-checkers key result)
          result)])))

 ;; Creates a transformer that expects pσ vs (so it can use yield-both or force if it needs to)
 ;; vs will have already been forced if necessary. Any types will have to be forced for non-abstract applications.
 (define ((mk-mk-simple mandatory mtypes op-rest return-out return-abs?) primitive widen?)
   (define arglist (generate-temporaries (map (λ _ #'v) mandatory)))
   (with-syntax* ([((rest ...) rest-arg (ap ...))
                   (if op-rest
                       #'((rest) rest (#%app apply))
                       #'(() '() (#%app)))]
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
     ;; mk-simple
     (λ (stx)
        (syntax-parse stx
          [(pσ vs)
            (with-syntax ([(force-clauses ...)
                            (for/list ([t (in-list mtypes)]
                                       [arg (in-list arglist)]
                                       #:when (eq? t 'any))
                              #`[#,arg #:in-force pσ #,arg])])
               (quasisyntax/loc stx
                 (match vs
                   [(list-rest args ... rest-arg)
                    (do (pσ) (force-clauses ...)
                      (cond [guard #,(return-out #'pσ)]
                            [else (yield (wrap (ap ... op args ... rest ...)))]))]
                   [_ (error 'mk-simple "Internal error ~a" vs)])))]))))

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

 (define-syntax-class (flat predfn) #:literals (->)
   #:attributes (checker-fn mk-simple (ts 1) arity type)
   (pattern (ts:basic ... (~optional (~seq #:rest r:basic)) -> t:basic)
            #:attr checker-fn (mk-checker predfn (attribute ts.type) (attribute r.type))
            #:attr mk-simple (mk-mk-simple (attribute ts.is-abs?)
                                           (attribute ts.type)
                                           (attribute r.is-abs?)
                                           (attribute t.abs-out)
                                           (attribute t.is-abs?))
            #:with arity (let ([mandatory (length (attribute ts.type))])
                           (if (attribute r)
                               #`(arity-at-least #,mandatory)
                               #`#,mandatory))
            #:attr type (if (attribute r)
                            (type-rest-arrow (attribute ts.type) (attribute r.type) (attribute t.type))
                            (type-arrow (attribute ts.type) (attribute t.type)))))

 (define-syntax-class (type predfn)
   #:attributes (checker-fn mk-simple arity)
   (pattern (~var f (flat predfn))
            #:attr checker-fn (attribute f.checker-fn)
            #:attr mk-simple (attribute f.mk-simple)
            #:with arity #'f.arity)
   (pattern ((~var fs (flat predfn)) ...)
            #:with arity #'(list fs.arity ...)
            #:attr checker-fn
            (λ (_)
               (define key
                 (map (match-lambda [(type-arrow in out) (list in #f)]
                                    [(type-rest-arrow in rest out) (list in rest)])
                      (attribute fs.type)))
               (cond
                [(hash-ref type-checkers key #f) => car]
                [else
                 (define result
                   (cons
                    (generate-temporary #'checker-multi)
                    #`(tλ (prim apply? v-addrs)
                        (expect-do-values #:values 1
                          #,(for/fold
                                ([stx ;; If nothing matches, log error
                                  #`(begin
                                      (prim-arity-error prim '#,(map length (attribute fs.ts)) (length v-addrs))
                                      (do-values ∅))])
                                ([checker (in-list (reverse (attribute fs.checker-fn)))])
                              (define checker* (checker #t #;multi-arity))
                              (with-syntax ([check-name (if (identifier? checker*)
                                                            checker*
                                                            (car checker*))])
                                #`(do-comp #:bind (res)
                                           (tapp check-name prim apply? v-addrs)
                                           (if (∅? res)
                                               #,stx
                                               (do-values res)))))))))
                 (hash-set! type-checkers key result)
                 result]))
            #:attr mk-simple
            (λ (widen?) (error 'mk-primitive-meaning "Simple primitives cannot have many arities."))))

(define-syntax-class access
  #:attributes (tag)
  (pattern #:ro #:attr tag 'read-only)
  (pattern #:rw #:attr tag 'read/write)
  (pattern #:no #:attr tag 'simple)
  (pattern #:!! #:attr tag 'full))

 (define-syntax-class (prim-entry predfn)
   #:attributes (prim access meaning checker-fn arity)
   (pattern [prim:id
             (~or
              (~seq #:predicate p:basic (~bind [access 'read-only]))
              (~seq
               (~or (~and #:simple (~bind [access 'read-only]))
                    (~seq acc:access implementation:id (~bind [access (attribute acc.tag)])))
               (~var t (type predfn))
               (~optional (~and #:widen widen?))))]
            #:fail-when (and (attribute implementation) (attribute widen?))
            "Cannot specify that a simple implementation widens when giving an explicit implementation."
            #:with arity (if (attribute p)
                             #'1
                             #'t.arity)
            #:attr checker-fn (or (and #:bind c (attribute t.checker-fn)
                                       (c #f))
                                  ;; must be a predicate
                                  ((mk-checker predfn '(any) #f) #f))
            ;; Either a special implementation is given, or
            ;; the implementation is for a type predicate,
            ;; or it is "simple" (i.e. type-directed)
            #:attr meaning (or (attribute implementation)
                               (and (attribute p)
                                    ;; generate predicate
                                    (syntax-parser
                                      [(pσ vs)
                                       #`(do (pσ) ([v #:in-force pσ (car vs)]
                                                   [res (in-list
                                                         (if (eq? v ●)
                                                             '(#t #f)
                                                             (list #,(predfn (attribute p.type) #'v))))])
                                           (yield res))]))
                               ((attribute t.mk-simple) #'prim (syntax? (attribute widen?)))))))

(define-syntax (mk-static-primitive-functions stx)
  (set! type-checkers (make-hash))
  (syntax-parse stx
    [(_ primitive?:id arities:id
        ((~var p (prim-entry list)) ...))
     (quasitemplate/loc stx
       (begin (define (primitive? o)
                (case o [(p.prim) #t] ... [else #f]))
              (define arities
                (hasheq (?@ 'p.prim p.arity) ...))))]))

(define-for-syntax (mk-checker-fns chk)
  (define names
    (for/list ([checker (in-list chk)])
      (if (identifier? checker)
          checker
          (car checker))))
  (define defs
    (for/list ([(_ pair) (in-hash type-checkers)])
      #`(define #,(car pair) #,(cdr pair))))
  (list defs names))

(define-syntax (mk-primitive-meaning stx)
  (set! type-checkers (make-hash))
  (syntax-parse stx
    [(_ cb?:boolean gσ?:boolean 0b?:boolean
        mean:id compile:id co:id clos?:id rlos?:id kont?:id
        (extra ...)
        defines ... ((~var p (prim-entry (type->pred-stx #'clos? #'rlos? #'kont?))) ...))
     (define compiled? (syntax-e #'cb?))
     (define 0cfa? (syntax-e #'0b?))
     (define ((ap m) arg-stx)
       (if (procedure? m)
           (m arg-stx)
           (datum->syntax arg-stx (cons m arg-stx) arg-stx)))
     (with-syntax ([((type-filters ...)
                     (checker-names ...)) (mk-checker-fns (attribute p.checker-fn))]
                   [(extra-ids ...) (generate-temporaries #'(extra ...))]
                   [(σ-gop ...) (if (syntax-e #'gσ?) #'() #'(pσ))]
                   [(δ-op ...) (if 0cfa? #'() #'(δ))])
       (define eval
         #`(case o
             #,@(for/list ([p (in-list (syntax->list #'(p.prim ...)))]
                           [acc (in-list (attribute p.access))]
                           [m (in-list (map ap (attribute p.meaning)))]
                           [checker (in-list (syntax->list #'(checker-names ...)))])
                  #`[(#,p)
                     (λP (pσ apply? ℓ δ k v-addrs)
                         (with-prim-yield
                          k
                          ;; Checkers will force what they need to and keep the rest
                          ;; lazy. Forced values are exploded into possible
                          ;; argument combinations
                          (do (pσ) ()
                            (do-comp #:bind (#:σ nσ vss)
                                     (tapp #,checker '#,p apply? v-addrs)
                                     (do (nσ) ([vs (in-set vss)])
                                       #,(cond [(eq? 'read/write acc) (m #'(nσ ℓ δ vs))]
                                               [(eq? 'read-only acc) (m #'(nσ vs))]
                                               [(eq? 'simple acc) (m #'(vs))]
                                               [(eq? 'full acc) (m #'(nσ ℓ δ k vs))]))))))])))
       (define qs #'quasisyntax) ;; have to lift for below to parse correctly
       (quasisyntax/loc stx
         (begin
           ;; Let primitives yield single values instead of entire states.
           (define-syntax (with-prim-yield syn)
             (syntax-parse syn
               [(_ k body)
                (define yield-tr (syntax-parameter-value #'yield))
                (define new
                  (λ (sx)
                     (syntax-parse sx
                       [(_ v)
                        (yield-tr (syntax/loc sx (yield (co target-σ k v))))])))
                ;; Must quote the produced quasisyntax's unsyntax
                #,#'#`(syntax-parameterize ([yield #,new]
                                            [original-yield
                                             (λ (stx)
                                                (printf "Orig in ~a~%" (syntax->datum stx))
                                                (define res (#,yield-tr stx))
                                                (printf "Orig out ~a~%" (syntax->datum res))
                                                res)])
                        body)]))
           defines ...
           type-filters ...
           ;; λP very much like λ%
           (define-syntax-rule (... (λP (pσ apply? ℓ δ k v-addrs) body ...))
             #,(if compiled?
                   #`(tλ (#:σ pσ apply? ℓ δ-op ... k v-addrs)
                       (bind-extra-prim (ℓ extra-ids ...)
                         body (... ...)))
                   #'(syntax-parameterize ([target-σ (make-rename-transformer #'σ-gop)] ...)
                       body (... ...))))
           ;; Identity if not compiled.
           (define-syntax-rule (compile o)
             #,(if compiled? eval #'o))
           (define mean
             (tλ (#:σ pσ o apply? ℓ δ-op ... k v-addrs)
                 #,(if compiled?
                       #'(tapp o #:σ pσ apply? ℓ δ-op ... k v-addrs)
                       eval))))))]))
