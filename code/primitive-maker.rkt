#lang racket

(require "data.rkt" "notation.rkt" "do.rkt" "parameters.rkt"
         (for-syntax syntax/parse racket/syntax
                     #;racket/match (except-in racket/match match match* define/match)
                     racket/list (except-in racket/base and)
                     syntax/parse/experimental/template
                     racket/pretty
                     syntax/id-table
                     (except-in racket/set for/set for*/set)
                     "notation.rkt")
         racket/splicing
         racket/trace
         racket/unsafe/ops
         racket/stxparam)
(provide getter widen yield prim-extras alt-reverse arity-error
         mk-primitive-meaning mk-static-primitive-functions
         ;; for use only by primitives.rkt
         original-yield mk-pull-arguments)

;; Extra hidden parameters prim-meaning might need.
(define-syntax-parameter prim-extras '())
;; General lookup and flat value widening
(define-syntax-parameter getter #f)
(define-syntax-parameter widen #f)
;; If 'apply'ing a list and we're in concrete mode
;; (actually using the built-in primitive) then we need a way to go
;; from consv (see reify-list). #f if we can't.
(define-syntax-parameter interpret-list
  (syntax-rules () [(_ σ v) (do-values #f)]))
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

(define (arity-error f l exp giv vals)
  (log-info "Arity error on ~a at ~a. Expected ~a args, given ~a: ~a" f l exp giv vals))

(define (prim-bad-input prim arg val)
  (log-info "Bad input to primitive: ~a (arg ~a): ~a" prim arg val))

(define (prim-bad-rest prim arg val)
  (log-info "Bad input to primitive: ~a (rest arg ~a): ~a" prim arg val))

(define (prim-arity-error prim expected given)
  (log-info "Primitive application arity mismatch ~a: expect: ~a, given ~a"
            prim expected given))

(define (log-non-nil-apply-tail v)
  (log-info "Primitive applied with non-nil terminated list: ~a" v))

(define (log-exn-in p ex)
  (log-info "Primitive raised exception ~a: ~a" p ex))

(define (mk-expect n)
  (cond [(exact-nonnegative-integer? n) (values (λ (n) (<= n 0)) sub1 values)]
        [else (values null? (λ (x) (if (pair? x) (cdr x) '())) length)]))

(define (log-too-many expect given)
  (log-info "'apply'd function given too many arguments (expected ~a): (>= ~a)"
            expect given))

(define (log-too-few expect given)
  (log-info "'apply'd function given too few arguments (expected ~a): ~a"
            expect given))

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
   ;; "any" types don't get forced unless the implementation decides to.
   ;; this cuts down on the state fan-out problem.
   ;; If not any, get all values and filter out only the ones that match
   ;; the type.
   ;; If nothing matches, we have a stuck state, and possibly log an error.
   (define (type-match t tmσ addr)
     (λ (acc on-err)
        (define body
          (cond
           [(eq? t 'any)
            #`(bind-delay (res #,tmσ addr)
                          (do-values (cons res #,acc)))]
           [else
            #`(bind-get (gres #,tmσ addr)
                        (let* ([filtered
                                (for/join1 ([v (in-abstract-values gres)] #:when #,(predfn t #'v)) v)]
                               [#,acc (cons filtered #,acc)])
                          #,@(listy (and on-err
                                         #`(when (is-nothing? filtered)
                                             #,(on-err #'gres))))
                          (do-values #,acc)))]))
        #`(let ([addr #,addr]) #,body)))

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
              (define tm (type-match t #'σ v))
              #`(do-comp #:bind/extra (#:σ σ acc)
                         #,(tm #'acc
                               (and (not mult-ary?)
                                    (λ (tmp)
                                       #`(prim-bad-input prim #,argnum #,tmp))))
                         #,stx)))
          (define check-rest
            (and rest
                 (type-match rest #'σ #'ra)))
          (define result
            (list
             (generate-temporary #'checker-mk-checker)
             #`(tλ (#:σ σ prim v-addrs)
                 (expect-do-values #:values 1 #:extra
                   (match v-addrs
                     [(list-rest vids ... rest-match)
                      #,(if rest
                            #`(do (σ) loop ([raddrs #,r-id]
                                            [acc '()]
                                            [argnum #,(length ts)])
                                  (match raddrs
                                    ['() (let ([acc (alt-reverse acc)]) #,built)]
                                    [(cons ra rrest)
                                     (do-comp #:bind/extra (#:σ σ acc)
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
 (define ((mk-mk-simple mandatory
                        mtypes
                        op-rest
                        op-rest-type
                        return-out) primitive primitive-alt exn-stx widen?)
   (define arglist (generate-temporaries (map (λ _ #'v) mandatory)))
   (define catch-tr
     (if exn-stx
         (λ (syn) #`(let ([quit (tλ () (continue))])
                      (with-handlers ([#,exn-stx (λ (ex)
                                                    (log-exn-in '#,primitive ex)
                                                    (tapp quit))])
                        #,syn)))
         values))
   (with-syntax ([((rest-op ...) rest-arg (ap ...))
                   (if op-rest
                       #'((rest) rest (#%app apply))
                       #'(() '() (#%app)))]
                  [(args ...) arglist]
                  [mand-guard
                   #`(or #,@(for/list ([m (in-list mandatory)]
                                       [arg (in-list arglist)])
                              (m arg)))]
                  [non-ap-rest-guard
                   #`(or #,@(listy (and op-rest
                                        #`(for/or ([v (in-list rest)])
                                            #,(op-rest #'v)))))]
                  [wrap (if widen? #'widen #'values)]
                  [op (or primitive-alt primitive)])
     ;; Common code for apply/not
     (define (non-apply stx pσ vs)
       (with-syntax* ([pσ pσ]
                      [vs vs]
                      ;; The checker forced all non-any positions
                      [(force-clauses ...)
                       (for/list ([t (in-list mtypes)]
                                  [arg (in-list arglist)]
                                  #:when (eq? t 'any))
                         #`[#,arg #:in-force pσ #,arg])])
         (quasisyntax/loc stx
           (match vs
             [(list-rest args ... rest-arg)
              (do (pσ) (force-clauses ...)
                (cond [(or mand-guard non-ap-rest-guard) #,(return-out #'pσ)]
                      [else #,(catch-tr #'(yield (wrap (ap ... op args ... rest-op ...))))]))]
             [_ (error 'mk-simple "Internal error ~a ~a" vs
                       '#,(for/list ([t (in-list mtypes)])
                            (match t
                              [(type-union ts) (cons '∪ ts)]
                              [_ t])))]))))
     ;; mk-simple
     (λ (stx)
        (syntax-parse stx
          [(pσ vs) (non-apply stx #'pσ #'vs)]))))

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
   (pattern (ts:basic ... (~optional (~seq #:rest r:basic))
             -> t:basic)
            #:attr checker-fn (mk-checker predfn (attribute ts.type) (attribute r.type))
            #:attr mk-simple (mk-mk-simple (attribute ts.is-abs?)
                                           (attribute ts.type)
                                           (attribute r.is-abs?)
                                           (attribute r.type)
                                           (attribute t.abs-out))
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
   ;; XXX: Deprecate
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
                   (list
                    (generate-temporary #'checker-multi)
                    #`(tλ (prim v-addrs)
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
                                ;; FIXME: Unsound for apply
                                #`(begin
                                    (printf "UGH NOOO~%")
                                    (do-comp #:bind (res)
                                           (tapp check-name prim v-addrs)
                                           (if (is-nothing? res)
                                               #,stx
                                               (do-values res))))))))))
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
                    (~seq #:simple-alternative prim-alt:id (~bind [access 'read-only]))
                    (~seq acc:access implementation:id (~bind [access (attribute acc.tag)])))
               (~var t (type predfn))
               (~optional (~and #:widen widen?))
               (~optional (~seq #:guard exn?:id))))]
            #:fail-when (and (attribute implementation) (attribute widen?))
            "Cannot specify that a simple implementation widens when giving an explicit implementation."
            #:with arity (if (attribute p)
                             #'1 ;; predicates are unary
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
                                                         (if (or (eq? v ●) (eq? v qdata^))
                                                             '(#t #f)
                                                             (list #,(predfn (attribute p.type) #'v))))])
                                           (yield res))]))
                               ((attribute t.mk-simple)
                                #'prim
                                (attribute prim-alt)
                                (attribute exn?)
                                (syntax? (attribute widen?)))))))

(define-for-syntax (populate-aliases origs aliases)
  (define alias-table (make-free-id-table))
  (for ([orig (in-list (syntax->list origs))]
        [alias (in-list (syntax->list aliases))])
    (free-id-table-set! alias-table orig (set-add (free-id-table-ref alias-table orig (set)) alias)))
  (define (aliases-of p) (set->list (free-id-table-ref alias-table p (set))))
  aliases-of)

(define-syntax (mk-static-primitive-functions stx)
  (set! type-checkers (make-hash))
  (syntax-parse stx
    [(_ primitive?:id arities:id
        ((~var p (prim-entry list)) ...)
        ([origs:id aliases:id] ...))
     (define aliases-of (populate-aliases #'(origs ...) #'(aliases ...)))
     (with-syntax* ([((aliasess ...) ...) (map aliases-of (attribute p.prim))]
                    [((alias* arity*) ...)
                     (for/fold ([acc '()]) ([aliass (in-list (syntax->list #'((aliasess ...) ...)))]
                                            [arity (in-list (attribute p.arity))])
                       (for/fold ([acc acc]) ([alias (in-list (syntax->list aliass))])
                         (cons (list alias arity) acc)))])
       (quasitemplate/loc stx
         (begin (define (primitive? o)
                  (case o [(p.prim aliasess ...) #t] ... [else #f]))
                (define arities
                  (hasheq (?@ 'p.prim p.arity) ...
                          (?@ 'alias* arity*) ...)))))]))

(define-for-syntax (mk-checker-fns chk)
  (define names
    (for/list ([checker (in-list chk)])
      (if (identifier? checker)
          checker
          (car checker))))
  (define defs
    (for/list ([(_ tcs) (in-hash type-checkers)])
      (match-define (list name body) tcs)
      #`(define #,name #,body)))
  (list defs names))

(define setnull (set '()))
(define-syntax-parameter toSetOfLists #f)
;; Combinatorial combination of arguments
(define-syntax-rule (mk-toSetOfLists name)
  (begin
  (define/match (name list-of-abstract-values)
    [('()) setnull]
    [((cons hdS tail))
     (for*/set ([hd (in-abstract-values hdS)]
                [restlist (in-set (name tail))])
       (cons hd restlist))])
  ;;(trace name)
  ))

(define-syntax (mk-primitive-meaning stx)
  (set! type-checkers (make-hash))
  (syntax-parse stx
    [(_ cb?:boolean gσ?:boolean 0b?:boolean
        mean:id compile:id ev:id co:id ap:id clos?:id rlos:id kont?:id
        (extra ...)
        (~bind [rlos? (format-id #'rlos "~a?" #'rlos)]
               [rlos: (format-id #'rlos "~a:" #'rlos)])
        defines ...
        ((~var p (prim-entry (type->pred-stx #'clos? #'rlos? #'kont?))) ...)
        ([origs:id aliases:id] ...))
     (define compiled? (syntax-e #'cb?))
     (define 0cfa? (syntax-e #'0b?))
     (define ((apm m) arg-stx)
       (if (procedure? m)
           (m arg-stx)
           (datum->syntax arg-stx (cons m arg-stx) arg-stx)))
     (define aliases-of (populate-aliases #'(origs ...) #'(aliases ...)))
     (match-define (list ltype-filters lchecker-names)
                   (mk-checker-fns (attribute p.checker-fn)))
     (with-syntax ([(type-filters ...) ltype-filters]
                   [(checker-names ...) lchecker-names]
                   [(extra-ids ...) (generate-temporaries #'(extra ...))]
                   [(σ-gop ...) (if (syntax-e #'gσ?) #'() #'(pσ))]
                   [(δ-op ...) (if 0cfa? #'() #'(δ))]
                   [(checkers-no-dup ...)
                    (let ([fid (make-free-id-table)])
                      (for/list ([checker-name (in-list lchecker-names)]
                                 #:unless (free-id-table-ref fid checker-name #f))
                        (free-id-table-set! fid checker-name #t)
                        checker-name))])
       (define eval
         #`(case o
             #,@(for/list ([p (in-list (syntax->list #'(p.prim ...)))]
                           [acc (in-list (attribute p.access))]
                           [m (in-list (map apm (attribute p.meaning)))]
                           [checker (in-list (syntax->list #'(checker-names ...)))])
                  (with-syntax
                      ([(args ...)
                        (case acc
                          [(read/write) #'(pσ ℓ δ vs)]
                          [(read-only) #'(pσ vs)]
                          [(simple) #'(vs)]
                          [(full) #'(pσ ℓ δ k vs)])])
                    #`[(#,p #,@(aliases-of p))
                       (λP (pσ fallv apply? ℓ δ k v-addrs)
                           (with-prim-yield
                            k
                            ;; Checkers will force what they need to and keep the rest
                            ;; lazy. Forced values are exploded into possible
                            ;; argument combinations
                            (do (pσ) ()
                              (cond [(and apply? fallv)
                                     (tapp call-rlos fallv ℓ δ-op ... k v-addrs)]
                                    [else
                                     (do-comp #:bind/extra (vss)
                                       (tapp #,checker '#,p v-addrs)
                                       (begin
                                         (unless (set? vss) (error 'primset))
                                         (do (pσ) ([vs (in-set vss)]) ;; set of lists of arguments
                                         #,(m #'(args ...)))))]))))]))))
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
                                            [original-yield #,yield-tr])
                        body)]))
           (define call-rlos
             (tλ (#:σ σ fnv ℓ δ-op ... k v-addrs)
               (match-function fnv
                 [(rlos: xs r e ρ)
                  (do-comp #:bind/extra (#:σ rσ apply-addrs)
                           (tapp pull-arguments-from-addresses #:σ σ xs #t ℓ δ-op ... v-addrs)
                           (if apply-addrs
                               (do (rσ)
                                   ([(ρ* σ*-aclos δ*) #:bind-rest-apply ρ rσ ℓ δ xs r apply-addrs])
                                 (yield (ev σ*-aclos e ρ* k δ*)))
                               (continue)))]
                 [_ (error 'apply "Bad fallback ~a" fnv)])))
           (mk-pull-arguments pull-arguments-from-addresses (δ-op ...) #t)
           defines ...
           (mk-toSetOfLists internalTSoL)
           (splicing-syntax-parameterize ([toSetOfLists (make-rename-transformer #'internalTSoL)])
             type-filters ...
             ;;(trace checker-names) ...
             )
           ;; λP very much like λ%
           (define-syntax-rule (... (λP (pσ fallv apply? ℓ δ k v-addrs) body ...))
             #,(if compiled?
                   #`(tλ (#:σ pσ fallv apply? ℓ δ-op ... k v-addrs)
                       (bind-extra-prim (ℓ extra-ids ...)
                         body (... ...)))
                   #'(syntax-parameterize ([target-σ (make-rename-transformer #'σ-gop)] ...)
                       body (... ...))))
           ;; Identity if not compiled.
           (define-syntax-rule (compile o)
             #,(if compiled? eval #'o))
           (define mean
             (tλ (#:σ pσ o fallv apply? ℓ δ-op ... k v-addrs)
                 #,(if compiled?
                       #'(tapp o #:σ pσ fallv apply? ℓ δ-op ... k v-addrs)
                       eval))))))]))

(define-simple-macro* (mk-pull-arguments name:id (δ-op ...) addrs?:boolean)
  (define name
    (tλ (#:σ iapσ num rest? l δ-op ... vs)
      (expect-do-values #:values 1 #:extra
        (define-values (no-expect? sub-expect len-expect) (mk-expect num))
        (do (iapσ) loop ([args vs] [raddrs '()] [i 0] [n num])
            (match args
              ['() (do-values (alt-reverse raddrs))]
              [(list arg)
               ;; The last argument should contain a list of extra arguments to pull on.
               ;; If n > 0 we must ensure there are enough values in the list to get.
               ;; If arg contains a list longer than n and rest? = #f then log error.
               ;; If rest? = #t then the remainder of the list is in the last in the addresses.
               (cond
                [(no-expect? n)
                 (cond [rest?
                        (define addr (make-apply-contour l i δ))
                        (do (iapσ) (#,(if (syntax-e #'addrs?)
                                          #'[bσ #:alias iapσ addr arg]
                                          #'[bσ #:join-forcing iapσ addr arg]))
                          (do-values (alt-reverse (cons addr raddrs))))]
                       [else (do-values (alt-reverse raddrs))])]
                [else
                 (define-values (addrs raddrs*)
                   (let aloop ([i i] [n n] [addrs '()] [raddrs raddrs])
                     (define addr (make-apply-contour l i δ))
                     (if (no-expect? n)
                         (if rest?
                             (values (alt-reverse (cons addr addrs)) (cons addr raddrs))
                             (values (alt-reverse addrs) raddrs))
                         (aloop (add1 i) (sub-expect n) (cons addr addrs) (cons addr raddrs)))))
                 (log-debug "Generated addrs (num: ~a, rest?: ~a) ~a ~a" num rest? addrs raddrs*)
                 (define result (box #f))
                 (do-comp #:bind/extra ()
                          (do (iapσ) (#,(if (syntax-e #'addrs?)
                                            #'[varg #:in-get iapσ arg]
                                            #'[varg #:in-force iapσ arg]))
                            ;; Make temporary addresses for apply at this application point
                            ;; and put all pullable arguments into their locations.
                            (do (iapσ) iloop ([last varg] [-addrs addrs] [i i] [n n])
                                (match last
                                  [(consv A D)
                                   (match -addrs
                                     [(cons addr -addrs)
                                      (cond
                                       [(no-expect? n) ;; too many in rest-arg list?
                                        (cond
                                         [rest? ;; nope, just include this in the final list.
                                          (unless (null? -addrs)
                                            (error 'apply "Too many addresses generated ~a" addrs))
                                          (do (iapσ) ([aprσ #:join iapσ addr (singleton last)])
                                            (set-box! result #t)
                                            (continue))]
                                         [else ;; yes, too many
                                          (log-too-many (len-expect num) (add1 i))
                                          (continue)])]
                                       [else
                                        ;; Still expect more, so pull another out.
                                        (do (iapσ) ([apjσ #:alias iapσ addr A]
                                                    [next #:in-get apjσ D])
                                          (iloop apjσ next -addrs (add1 i) (sub-expect n)))])]
                                     [_
                                      (log-too-many (len-expect num) (add1 i))
                                      (continue)])]
                                  [v
                                   (unless (null? v)
                                     (log-non-nil-apply-tail v))
                                   (cond
                                    [(no-expect? n)
                                     (set-box! result #t)
                                     (if rest?
                                         ;; Actually nothing. Make the tail an empty list.
                                         (do (iapσ) ([apnσ #:join iapσ (car -addrs) snull])
                                           (continue))
                                         ;; No tail since not for rest-args.
                                         (continue))]
                                    [else
                                     ;; Can't pull anything out of empty!
                                     (log-too-few (len-expect num) i)
                                     (continue)])])))
                          (do-values (and (unbox result)
                                          (alt-reverse raddrs*))))])]
              ;; Explicitly given arguments
              [(cons arg args)
               (define addr (make-apply-contour l i δ))
               (cond [(and (no-expect? n) (not rest?)) ;; might we have too many arguments?
                      (log-info "'apply'd function given too many arguments (>= ~a) (expected ~a)"
                                i (len-expect num))
                      (do-values #f)]
                     [else
                      (do (iapσ) (#,(if (syntax-e #'addrs?)
                                        #'[bσ #:alias iapσ addr arg]
                                        #'[bσ #:join-forcing iapσ addr arg]))
                        (loop bσ args (cons addr raddrs) (add1 i) (sub-expect n)))])]))))))