#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt" "primitives.rkt" "parse.rkt"
         "notation.rkt" "op-struct.rkt" "do.rkt"
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax)
         racket/stxparam racket/splicing
         racket/trace)
(provide yield-meaning mk-analysis)

;; Yield is an overloaded term that will do some manipulation to its
;; input. Yield-meaning is the intended meaning of yield.
(define-syntax-parameter yield-meaning
  (λ (stx) (raise-syntax-error #f "Must parameterize for mk-analysis" stx)))

(define (toSetOfLists list-of-sets)
  (match list-of-sets
    ['() snull]
    [(cons hdS tail)
     (for*/set ([hd (in-set hdS)]
                [restlist (in-set (toSetOfLists tail))])
       (cons hd restlist))]))

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
         (~optional (~or (~and #:σ-passing σ-passing?)
                         (~and #:global-σ global-σ?)))
         (~optional (~and #:wide wide?))
         (~optional (~or (~and (~seq #:kcfa k-nat-or-∞)
                               (~bind [K (syntax-e #'k-nat-or-∞)]))
                         (~and #:1cfa (~bind [K 1])))
                    #:defaults ([K 0]))
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
                   ;; represent σ explicitly in all states?
                   [(σ-op ...) (if (given wide?) #'() #'(σ))]
                   ;; explicitly pass σ/∆ to compiled forms?
                   [(σ-gop ...) (if σ-threading? #'(σ) #'())]
                   [(cs-uop ...) (if (and (given compiled?) (given set-monad?)) #'(target-cs) #'())]
                   [(cs-bop ...) (if (and (given compiled?) (given set-monad?)) #'(cs) #'())]
                   ;; If σ not part of state and not global, it is passed
                   ;; in as (cons σ state), so expand accordingly.
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
              (λ% (σ ρ k δ)
                  (do (σ) ([v (delay σ (lookup-env ρ x))])
                    (yield (co σ k v))))]
             [(datum l d) (λ% (σ ρ k δ) (do (σ) () (yield (co σ k d))))]
             [(primr l which)
              (define p (primop which))
              (λ% (σ ρ k δ) (do (σ) () (yield (co σ k p))))]
             [(lam l x e)
              (define c (compile e))
              (define fv (free e))
              (λ% (σ ρ k δ) (do (σ) () (yield (co σ k (clos x c ρ fv)))))]
             [(lrc l xs es b)
              (define c (compile (first es)))
              (define cs (map compile (rest es)))
              (define cb (compile b))
              (define x (first xs))
              (define xs* (rest xs))
              (define ss (map (λ _ ∅) xs))
              (λ% (σ ρ k δ)
                  (define as (map (λ (x) (make-var-contour x δ)) xs))
                  (define/ρ ρ* (extend* ρ xs as))
                  (do (σ) ([(σ0 a) #:push σ l δ k]
                           [σ*-lrc #:join* σ0 as ss])
                    (yield (ev σ*-lrc c ρ* (lrk x xs* cs cb ρ* a δ) δ))))]
             [(app l e es)
              (define c (compile e))
              (define cs (map compile es))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-app a) #:push σ l δ k])
                    (yield (ev σ*-app c ρ (ls l 0 cs '() ρ a δ) δ))))]
             [(ife l e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-ife a) #:push σ l δ k])
                    (yield (ev σ*-ife c0 ρ (ifk c1 c2 ρ a δ) δ))))]
             [(st! l x e)
              (define c (compile e))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-st! a) #:push σ l δ k])
                    (yield (ev σ*-st! c ρ (sk! (lookup-env ρ x) a) δ))))]
             [(primr l which) (define p (primop which))
              (λ% (σ ρ k δ) (do (σ) () (yield (co σ k p))))])))

       (define compile-def
         (cond [(attribute compiled?)
                (define hidden-σ (and (given σ-∆s?) (not (given global-σ?)) (generate-temporary #'hidden)))
                (with-syntax ([(top ...) (listy hidden-σ)]
                              [topp (or hidden-σ #'σ)])
                  (quasisyntax/loc stx
                    ((define-syntax-rule (... (λ% (σ ρ k δ) body ...))
                       (λ (top ... σ-gop ... ρ-op ... k δ-op ... cs-bop ...)
                          (syntax-parameterize ([yield (... (... #,yield-ev))]
                                                [top-σ (make-rename-transformer #'topp)]
                                                [target-σ (make-rename-transformer #'σ)]
                                                [cs-uop (make-rename-transformer #'cs-bop)] ...
                                                [target-cs-given? (and #'cs-bop #t)] ... ;; hack
                                                [top-σ? #t])
                            body (... ...))))
                     (define (compile e) #,eval))))]
               [else
                ;; brittle, since other identifiers must be the same in ev:
                (syntax/loc stx
                  ((... (define-syntax-rule (λ% (σ ρ k δ) body ...)
                          (generator body ...)))
                   (define compile values)))]))

       (quasisyntax/loc stx
         (begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct co (σ k v) (σ-op ... k v) expander-flags ...)
           (mk-op-struct ans (σ v) (σ-op ... v) expander-flags ...
                         #:expander-id ans:)
           (mk-op-struct ap (σ l fn-addr v-addrs k δ)
                         (σ-op ... l fn-addr v-addrs k δ-op ...)
                         expander-flags ...)
           (struct mt () #:prefab)
           (struct sk! (x k) #:prefab)
           (struct primop (which) #:prefab)
           (mk-op-struct ifk (t e ρ k δ) (t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (x xs es e ρ k δ) (x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (l n es vs ρ k δ) (l n es vs ρ-op ... k δ-op ...))
           (mk-op-struct clos (x e ρ free) (x e ρ-op ... free) #:expander-id clos:)

           
           #,@(if (given touches)
                  #`((mk-touches touches clos: #,(zero? (attribute K))))
                  #'())
           (splicing-syntax-parameterize ([target-σ? #,σ-threading?]
                                          [target-cs? #,c-passing?])
           (define-syntax do-macro
             (mk-do #,(given σ-∆s?)
                    #,c-passing?
                    #,(given global-σ?)
                    #,(given generators?)))
           (splicing-syntax-parameterize ([do (make-rename-transformer #'do-macro)])

           ;; ev is special since it can mean "apply the compiled version" or
           ;; make an actual ev state to later interpret.
           #,@(if (given compiled?)
                  (quasisyntax/loc stx
                    ((define-syntax (ev syn)
                       (syntax-case syn ()
                         ;; σ only optional if it's global
                         [(_ σ e ρ k δ)
                          #'(e #,@(listy (and (given σ-∆s?) #'top-σ))
                               σ-gop ... ρ-op ... k δ-op ... cs-uop ...)]))
                     (define-match-expander ev: ;; inert, but introduces bindings
                       (syntax-rules () [(_ . args) (list . args)]))))
                  (quasisyntax/loc stx
                    ((mk-op-struct ev (σ e ρ k δ) (σ-op ... e ρ-op ... k δ-op ...)
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

           ;; Let primitives yield single values instead of entire states.
           (define-syntax (with-prim-yield syn)
             (syntax-parse syn
               [(_ k body)
                (define yield-tr (syntax-parameter-value #'yield-meaning))
                (define new
                  (λ (sx)
                     (syntax-parse sx
                       [(_ v)
                        (yield-tr (syntax/loc sx (yield (co target-σ k v))))])))
                #`(syntax-parameterize ([yield #,new]) body)]))

           (define (inj e)
             (define σ₀ (hash))
             (generator
              (do (σ₀) () (yield (ev σ₀ (compile e) (hash) (mt) '())))))

           (define (aval e) (fixpoint step (inj e)))

           #,@compile-def

           (mk-prims prim-meaning clos?)
           ;; [Rel State State]
           (define (step state)
             (match state
               [(co: σ k v)
                (match k
                  [(mt) (generator (do (σ) ([v (force σ v)])
                                     (yield (ans σ v))))]

                  ;; We need this intermediate step so that σ-∆s work.
                  ;; The above join is not merged into the store until
                  ;; after the step, and the address is needed by the call.
                  [(ls: l n '() v-addrs ρ a δ)
                   (define v-addr (make-var-contour (cons l n) δ))
                   (define args (reverse (cons v-addr v-addrs)))
                   (generator
                    (do (σ) ([σ*-ls #:join σ v-addr (force σ v)]
                             [k (getter σ*-ls a)])
                      (yield (ap σ*-ls l (first args) (rest args) k δ))))]

                  [(ls: l n (list-rest e es) v-addrs ρ a δ)
                   (define v-addr (make-var-contour (cons l n) δ))
                   (generator
                    (do (σ) ([σ*-lsn #:join σ v-addr (force σ v)])
                      (yield (ev σ*-lsn e ρ
                                 (ls l (add1 n) es (cons v-addr v-addrs) ρ a δ) δ))))]
                  [(ifk: t e ρ a δ)
                   (generator
                    (do (σ) ([k* (getter σ a)]
                             [v (force σ v)])
                      (yield (ev σ (if v t e) ρ k* δ))))]
                  [(lrk: x '() '() e ρ a δ)
                   (generator
                    (do (σ) ([σ*-lrk #:join σ (lookup-env ρ x) (force σ v)]
                             [k* (getter σ*-lrk a)])
                      (yield (ev σ*-lrk e ρ k* δ))))]
                  [(lrk: x (cons y xs) (cons e es) b ρ a δ)
                   (generator
                    (do (σ) ([σ*-lrkn #:join σ (lookup-env ρ x) (force σ v)])
                      (yield (ev σ*-lrkn e ρ (lrk y xs es b ρ a δ) δ))))]
                  [(sk! l a)
                   (generator
                    (do (σ) ([σ*-sk! #:join σ l (force σ v)]
                             [k* (getter σ*-sk! a)])
                      (yield (co σ*-sk! k* (void)))))])]

               ;; v is not a value here. It is an address.
               [(ap: σ l fn-addr arg-addrs k δ)
                (generator
                 (do (σ) ([f (getter σ fn-addr)])
                   (match f
                     [(clos: xs e ρ _)
                      (cond [(= (length xs) (length arg-addrs))
                             (do (σ)
                                 ([(ρ* σ*-clos δ*) #:bind ρ σ l δ xs arg-addrs])
                               (yield (ev σ*-clos e ρ* k δ*)))]
                            ;; Yield the same state to signal "stuckness".
                            [else
                             ;;(printf "Arity error on ~a~%" f)
                             (yield (ap σ l fn-addr arg-addrs k δ))])]
                     [(primop o)
                      ;; Get all possible values for all arguments
                      (define all (for/list ([a (in-list arg-addrs)])
                                    (getter σ a)))
                      (with-prim-yield
                       k
                       ;; Analyze all combinations of these arguments
                       (do (σ) ([vs (in-set (toSetOfLists all))])
                         (prim-meaning o σ l δ vs)))]
                     [_
                      ;;(printf "Stuck (non-function) ~a~%" f)
                      (yield (ap σ l fn-addr arg-addrs k δ))])))]

               ;; this code is dead when running compiled code.
               [(ev: σ e ρ k δ)
                #,(if (given compiled?)
                      #'(generator (do (σ) () (yield (ev σ e ρ k δ))))
                      eval)]

               [(ans: σ v) (generator (do (σ) () (yield (ans σ v))))]
               [_ (error 'step "What? ~a" state)])))))))]))
