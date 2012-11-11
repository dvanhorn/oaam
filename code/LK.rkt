#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt" "primitives.rkt" "parse.rkt"
         "notation.rkt" "op-struct.rkt" "do.rkt" "add-lib.rkt"
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax racket/base
                     syntax/parse/experimental/template)
         racket/stxparam racket/splicing
         racket/trace)
(provide yield-meaning #;<-reprovide
         mk-analysis)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

(define-syntax (mk-analysis stx)
  (syntax-parse stx
    [(_ (~or ;; analysis parameters
         (~optional (~seq #:fixpoint fixpoint:expr)
                    #:defaults ([fixpoint #'fix]))
         (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
         (~once (~seq #:ans ans:id)) ;; name the answer struct to use/provide
         (~optional (~seq #:touches touches:id)) ;; Touch relation specialized for clos
         ;; Analysis strategies flags (requires the right parameters too)
         (~optional (~and #:compiled compiled?))
         (~optional (~and #:σ-∆s σ-∆s?))
         (~optional (~and #:sparse sparse?))
         (~optional (~or (~and #:σ-passing σ-passing?)
                         (~and #:global-σ global-σ?)))
         (~optional (~and #:wide wide?))
         (~optional (~or (~and (~seq #:kcfa k-nat-or-∞)
                               (~bind [K (syntax-e #'k-nat-or-∞)]))
                         (~and #:1cfa (~bind [K 1])))
                    #:defaults ([K 0]))
         (~optional (~seq #:prepare prep-fn:expr)) ;; any preprocessing?
         (~optional (~or (~and #:generators generators?)
                         (~and #:set-monad set-monad?)))) ...)
     #:do [(define-syntax-rule (given kw) (syntax? (attribute kw)))
           (define-syntax-rule (implies ante concl) (if ante concl #t))
           (define σ-threading? (or (given σ-passing?) (given σ-∆s?)))
           (define c-passing? (given set-monad?))]
     #:fail-unless (implies (given global-σ?) (given wide?))
     "Cannot globalize narrow stores."
     #:fail-unless (implies (given σ-∆s?) (given wide?))
     "Store deltas and narrow stores are antithetical."
     #:fail-unless (or (given fixpoint) (given set-monad?))
     "Cannot use a general fixpoint for step function that doesn't return sets."
     #:fail-when (and (given σ-passing?) (given global-σ?))
     "Cannot use store passing with a global store"
     (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                    (if (zero? (attribute K)) #'(() () ()) #'((ρ) (δ) (l)))]
                   [ev: (format-id #'ev "~a:" #'ev)]
                   [ev #'ev]
                   ;; represent rσ explicitly in all states?
                   [(σ-op ...) (if (given wide?) #'() #'(rσ))]
                   ;; explicitly pass σ/∆ to compiled forms?
                   [(σ-gop ...) (if σ-threading? #'(gσ) #'())]
                   ;; If rσ not part of state and not global, it is passed
                   ;; in as (cons rσ state), so expand accordingly.
                   [(expander-flags ...)
                    (cond [(and (given wide?) (not (given global-σ?)))
                           #'(#:expander #:with-first-cons)]
                          [else #'()])]
                   [inj-σ (if (given σ-∆s?) #''() #'(hash))])
       (define yield-ev
         (if (attribute compiled?)
             #'(λ (syn)
                   (syntax-parse syn #:literals (ev)
                     [(_ (ev . args)) (syntax/loc syn (ev . args))]
                     [(_ e:expr) (syntax/loc syn (yield-meaning e))]))
             #'(syntax-rules () [(_ e) (yield-meaning e)])))
       (define eval ;; what does ev mean?
         (syntax/loc stx
           (match e
             [(var l x)
              (λ% (ev-σ ρ k δ)
                  (define xaddr (lookup-env ρ x))
                  (do (ev-σ) ([v #:in-get ev-σ xaddr])
                    (match v
                      [(promise: e ρ*)
                       (do (ev-σ) ([(σ* a) #:push ev-σ l δ k])
                         (yield (ev σ* e ρ* (dmd xaddr a) δ)))]
                      [v (yield (co ev-σ k v))])))]
             [(datum l d) (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k d))))]
             [(primr l which)
              (define p (primop (compile-primop which)))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k p))))]
             [(lam l x e*)
              (define c (compile e*))
              (define fv (free e))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k (clos x c ρ fv)))))]
             ;; Lazy letrec does not evaluate its rhses until demanded.
             [(lrc l xs es b)
              (define cb (compile b))
              ;; Construct the specialized promises for arguments that are "trivial"
              ;; This implements section 3.1 of "Systematic Abstraction of Abstract Machines"
              (define args
                (for/list ([x (in-list xs)]
                           [e (in-list es)])
                  (match e
                    [(lam l x e*)
                     (define c (compile e*))
                     (define fv (free e))
                     (λ* (ρ δ) (clos x c ρ fv))]
                    [(datum l d) (λ* (ρ δ) d)]
                    [(primr l which)
                     (define p (primop (compile-primop which)))
                     (λ* (ρ δ) p)]
                    [(cons e es)
                     (define c (compile e))
                     (λ* (ρ δ) (promise c ρ))])))
              (λ% (ev-σ ρ k δ)
                  (define v-addrs (for/list ([x (in-list xs)]) (make-var-contour x δ)))
                  (define/ρ ρ* (extend* ρ xs v-addrs))
                  (do (ev-σ) ([(σ*-lrc a) #:push ev-σ l δ k])
                    (do (σ*-lrc) loop ([args args] [as v-addrs])
                      (match args
                        ['() (yield (ev σ*-lrc cb ρ* k δ))]
                        [`(,arg . ,args)
                         (do (σ*-lrc) ([σ* #:join σ*-lrc (car as) (singleton (ap* arg ρ* δ))])
                           (loop σ* args (cdr as)))]))))]
             ;; Lazy apply will delay its arguments, evaluate the function position,
             ;; and then evaluate under lambda.
             [(app l e es)
              (define c (compile e))
              (define-syntax-rule (mk-addr n δ) (make-var-contour (cons l n) δ))
              ;; Construct the specialized promises for arguments that are "trivial"
              ;; This implements section 3.1 of "Systematic Abstraction of Abstract Machines"
              (define rev-args
                (let loop* ([es es] [n 0] [rev-args '()])
                  (define-syntax-rule (loop es arg)
                    (loop* es (add1 n) (cons arg rev-args)))
                  (match es
                    ['() rev-args]
                    [`(,(lam l x e*) . ,es)
                     (define c (compile e*))
                     (define fv (free e))
                     (loop es
                           (λ^ (ρ δ) (values (mk-addr n δ) (clos x c ρ fv))))]
                    [`(,(datum l d) . ,es)
                     (loop es (λ^ (ρ δ) (values (mk-addr n δ) d)))]
                    [`(,(var l x) . ,es)
                     (loop es (λ^ (ρ δ) (values (lookup-env ρ x) #f)))]
                    [`(,(primr l which) . ,es)
                     (define p (primop (compile-primop which)))
                     (loop es
                           (λ^ (ρ δ) (values (mk-addr n δ) p)))]
                    [(cons e es)
                     (define c (compile e))
                     (loop es (λ^ (ρ δ) (values (mk-addr n δ) (promise c ρ))))])))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-app a) #:push ev-σ l δ k])
                    (do (σ*-app) loop ([rargs rev-args] [v-addrs '()])
                      (match rargs
                        ['() (yield (ev σ*-app c ρ (dly l v-addrs a δ) δ))]
                        [`(,arg . ,rargs)
                         (define-values (a v) (ap^ arg ρ δ))
                         (if v
                             (do (σ*-app) ([σ*arg #:join σ*-app a (singleton v)])
                               (loop σ*arg rargs (cons a v-addrs)))
                             (loop σ*-app rargs (cons a v-addrs)))]))))]
             ;; Lazy if is the same as strict if.
             [(ife l e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-ife a) #:push ev-σ l δ k])
                    (yield (ev σ*-ife c0 ρ (ifk c1 c2 ρ a δ) δ))))]
             [_ (error 'eval "Bad expr ~a" e)])))

       (define compile-def
         (cond [(attribute compiled?)
                (define hidden-σ (and (given σ-∆s?) (not (given global-σ?)) (generate-temporary #'hidden)))
                (with-syntax ([(top ...) (listy hidden-σ)]
                              [topp (or hidden-σ #'gσ)])
                  (quasisyntax/loc stx
                    ((define-syntax-rule (... (λ% (gσ ρ k δ) body ...))
                       (λ (top ... σ-gop ... ρ-op ... k δ-op ...)
                          (syntax-parameterize ([yield (... (... #,yield-ev))]
                                                [top-σ (make-rename-transformer #'topp)]
                                                [target-σ (make-rename-transformer #'gσ)]
                                                [top-σ? #t])
                            body (... ...))))
                     (define (compile e) #,eval))))]
               [else
                ;; brittle, since other identifiers must be the same in ev:
                (syntax/loc stx
                  ((... (define-syntax-rule (λ% (ev-σ ρ k δ) body ...)
                          (generator body ...)))
                   (define compile values)))]))

       (quasitemplate/loc stx
         (begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct co (rσ k v) (σ-op ... k v) expander-flags ...)
           (mk-op-struct ans (rσ v) (σ-op ... v) expander-flags ...
                         #:expander-id ans:)
           (mk-op-struct ap (rσ l fn-addr v-addrs k δ)
                         (σ-op ... l fn-addr v-addrs k δ-op ...)
                         expander-flags ...)
           (struct mt () #:prefab)
           (mk-op-struct ifk (t e ρ k δ) (t e ρ-op ... k δ-op ...))
           (mk-op-struct dly (l v-addrs k δ) (l v-addrs k δ-op ...)) ;; delay arguments
           (mk-op-struct dmd (a k) (a k)) ;; demanded binding
           (mk-op-struct dmp (l o at ad k δ) (l o at ad k δ-op ...)) ;; demand args for primop
           (mk-op-struct clos (xs e ρ free) (xs e ρ-op ... free) #:expander-id clos:)
           (mk-op-struct rlos (xs r e ρ free) (xs r e ρ-op ... free) #:expander-id rlos:)
           (define (kont? v) (or (dly? v) (dmd? v) (dmp? v) (ifk? v) (mt? v)))
           ;; values
           (mk-op-struct promise (e ρ) (e ρ-op ...))

           #,@(if (given touches)
                  #`((mk-touches touches clos: rlos: promise: #,(zero? (attribute K))))
                  #'())
           (splicing-syntax-parameterize ([target-σ? #,σ-threading?]
                                          [target-cs? #,c-passing?]
                                          [target-actions? #,(given sparse?)])
           (define-syntax do-macro
             (mk-do #,(given σ-∆s?)
                    #,c-passing?
                    #,(given global-σ?)
                    #,(given generators?)))
           (mk-flatten-value flatten-value-fn clos: rlos: kont?)
           (splicing-syntax-parameterize ([do (make-rename-transformer #'do-macro)]
                                          [flatten-value (make-rename-transformer #'flatten-value-fn)])

           ;; ev is special since it can mean "apply the compiled version" or
           ;; make an actual ev state to later interpret.
           #,@(if (given compiled?)
                  (quasisyntax/loc stx
                    ((define-syntax (ev syn)
                       (syntax-case syn ()
                         ;; gσ only optional if it's global
                         [(_ gσ e ρ k δ)
                          #'(e #,@(listy (and (given σ-∆s?) #'top-σ))
                               σ-gop ... ρ-op ... k δ-op ...)]))
                     (define-match-expander ev: ;; inert, but introduces bindings
                       (syntax-rules () [(_ . args) (list . args)]))))
                  (quasisyntax/loc stx
                    ((mk-op-struct ev (rσ e ρ k δ) (σ-op ... e ρ-op ... k δ-op ...)
                                   expander-flags ...))))

            (define-syntax-rule (define/ρ ρ body)
             #,(if (zero? (attribute K))
                   #'(void)
                   #'(define ρ body)))

           ;; No environments in 0cfa
           (define-syntax-rule (lookup-env ρ x)
             #,(cond [(zero? (attribute K)) #'x]
                     [else #'(hash-ref ρ x (λ () (error 'lookup "Unbound var ~a" x)))]))
           (...
            (define-syntax (generator syn)
              (syntax-parse syn
                [(_ body:expr ...)
                 (syntax/loc syn
                   (syntax-parameterize ([yield (... #,yield-ev)])
                     #,(cond [(given generators?)
                              (quasisyntax/loc stx
                                (... (real-generator () body ...)))]
                             [else
                              (quasisyntax/loc stx
                                (... (begin body ...)))])))])))

           (define (inj e)
             (define σ₀ (hash))
             (generator
              (do (σ₀) () (yield (ev σ₀ (compile e) (hash) (mt) '())))))

           (define (aval e #:prepare [prepare (?? prep-fn
                                                  (λ (e)
                                                     ;; Don't join literals when parsing for
                                                     ;; concrete evaluation.
                                                     (parameterize ([cons-limit
                                                                     #,(if (eq? (attribute K) +inf.0)
                                                                           #'+inf.0
                                                                           #'(cons-limit))])
                                                       (define-values (e* r) (parse-prog e gensym gensym))
                                                       ;; No basic library for LK machine
                                                       e*)))])
             (fixpoint step (inj (prepare e))))

           #,@compile-def
           (define-syntax-rule (... (λ^ (ρ δ) body ...))
             #,(if (zero? (attribute K))
                   #'(λ () body (... ...))
                   #'(λ (ρ δ) body (... ...))))
           (define-syntax-rule (... (λ* (ρ δ) body ...))
             #,(if (zero? (attribute K))
                   #'(let () body (... ...))
                   #'(λ (ρ δ) body (... ...))))
           (define-syntax-rule (... (ap^ l^ es ...))
             #,(if (zero? (attribute K))
                   #'(l^)
                   #'(l^ es (... ...))))
           (define-syntax-rule (... (ap* l^ es ...))
             #,(if (zero? (attribute K))
                   #'l^
                   #'(l^ es (... ...))))

           (define-syntax mk-prims (mk-mk-prims #,(given global-σ?) #,σ-threading?
                                                #,(given σ-∆s?) #,(given compiled?)
                                                #,(attribute K)))
           (mk-prims prim-meaning compile-primop co clos? rlos?)
           ;; [Rel State State]
           (define (step state)
             (match state
               [(co: co-σ k v)
                (match k
                  [(mt) (generator (do (co-σ) ([v #:in-force co-σ v])
                                     (yield (ans co-σ v))))]

                  [(dmd: va ka)
                   (generator (do (co-σ) ([σ*dmd #:join co-σ va (singleton v)]
                                          [k #:in-get σ*dmd ka])
                                (yield (co σ*dmd k v))))]

                  [(dly: l v-addrs ka δ)
                   (generator
                    (do (co-σ) ([fn #:in-force co-σ v])
                      (match fn
                        [(clos: xs e ρ _)
                         (cond [(= (length xs) (length v-addrs))
                                (do (co-σ)
                                    ([(ρ* σ*-clos δ*) #:bind ρ co-σ l δ xs v-addrs]
                                     [k #:in-get σ*-clos ka])
                                  (yield (ev σ*-clos e ρ* k δ*)))]
                               ;; Yield the same state to signal "stuckness".
                               [else
                                (log-info "Arity error on ~a at ~a" fn l)
                                (yield (co co-σ k v))])]
                        ;; Primop applications are tricky in lazy languages since
                        ;; we must force /all/ arguments to the primop. We choose to
                        ;; do this in left-to-right order. We find the first argument
                        ;; that needs forcing, and continue until all arguments are known
                        ;; to have forced values.
                        [(primop o)
                         (match v-addrs
                           ['() (do (co-σ) ([k #:in-get co-σ ka])
                                  (prim-meaning o co-σ l δ k '()))]
                           [(cons va at)
                            (define vs (getter co-σ va))
                            (define ad* (list va))
                            (do (co-σ) ([v (in-set vs)])
                              (match v
                                [(promise: e ρ)
                                 (yield (ev co-σ e ρ (dmp l o at ad* ka δ) δ))]
                                [_ (yield (co co-σ (dmp l o at ad* ka δ) v))]))])]
                        [_ (log-info "Applied non-function: ~a at ~a" fn l)
                           (yield (co co-σ k v))])))]

                  [(dmp: l o at (and (cons af _) ad) ka δ)
                   (generator
                   (do (co-σ) ([σ*dmp #:join-forcing co-σ af v])
                     (match at
                       ['() (define ad* (reverse ad))
                        (do (co-σ) ([k #:in-get co-σ ka])
                          (prim-meaning o co-σ l δ k ad*))]
                       [(cons va at)
                        (define vs (getter co-σ va))
                        (define k (dmp l o at (cons va ad) ka δ))
                        (do (co-σ) ([has-nonpromise? (in-set (∪1 (set #f) (not (for/and ([v (in-set vs)]) (promise? v)))))])
                          (if has-nonpromise?
                              (do (co-σ) ([v (delay co-σ va)])
                                (yield (co co-σ k v)))
                              (do (co-σ) ([v (in-set vs)])
                                (match v
                                  ;; at least one promise. Go force it.
                                  [(promise: e ρ) (yield (ev co-σ e ρ k δ))]
                                  [_ (continue)]))))])))]

                  [(ifk: t e ρ a δ)
                   (generator
                    (do (co-σ) ([k* #:in-get co-σ a]
                                [v #:in-force co-σ v])
                      (yield (ev co-σ (if v t e) ρ k* δ))))]
                  [_ (error 'step "Bad continuation ~a" k)])]

               ;; this code is dead when running compiled code.
               [(ev: ev-σ e ρ k δ)
                #,(if (given compiled?)
                      #'(generator (do (ev-σ) () (yield (ev ev-σ e ρ k δ))))
                      eval)]

               [(ans: ans-σ v) (generator (do (ans-σ) () (yield (ans ans-σ v))))]
               [_ (error 'step "Bad state ~a" state)]))

#;
           (trace step)

           )))))]))
