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
                  (do (ev-σ) ([v (delay ev-σ (lookup-env ρ x))])
                    (yield (co ev-σ k v))))]
             [(datum l d) (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k d))))]
             [(primr l which)
              (define p (primop (compile-primop which)))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k p))))]
             [(lam l x e*)
              (define c (compile e*))
              (define fv (free e))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k (clos x c ρ fv)))))]
             [(rlm l x r e*)
              (define c (compile e*))
              (define fv (free e))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k (rlos x r c ρ fv)))))]
             [(lrc l xs es b)
              (define c (compile (first es)))
              (define cs (map compile (rest es)))
              (define cb (compile b))
              (define x (first xs))
              (define xs* (rest xs))
              (define ss (map (λ _ nothing) xs))
              (λ% (ev-σ ρ k δ)
                  (define as (map (λ (x) (make-var-contour x δ)) xs))
                  (define/ρ ρ* (extend* ρ xs as))
                  (do (ev-σ) ([(σ0 a) #:push ev-σ l δ k]
                           [σ*-lrc #:join* σ0 as ss])
                    (yield (ev σ*-lrc c ρ* (lrk x xs* cs cb ρ* a δ) δ))))]
             [(app l e es)
              (define c (compile e))
              (define cs (map compile es))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-app a) #:push ev-σ l δ k])
                    (yield (ev σ*-app c ρ (ls l 0 cs '() ρ a δ) δ))))]
             [(ife l e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-ife a) #:push ev-σ l δ k])
                    (yield (ev σ*-ife c0 ρ (ifk c1 c2 ρ a δ) δ))))]
             [(st! l x e)
              (define c (compile e))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-st! a) #:push ev-σ l δ k])
                    (yield (ev σ*-st! c ρ (sk! (lookup-env ρ x) a) δ))))]
             ;; let/cc is easier to add than call/cc since we make yield
             ;; always make co states for primitives.
             [(lcc l x e)
              (define c (compile e))
              (λ% (ev-σ ρ k δ)
                  (define x-addr (make-var-contour x δ))
                  (define/ρ ρ* (extend ρ x x-addr))
                  (do (ev-σ) ([(σ*-lcc a) #:join ev-σ x-addr (singleton k)])
                    (yield (ev σ*-lcc c ρ* k δ))))]
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
                  ((... (define-syntax-rule (λ% (σ% ρ k δ) body ...)
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
           (struct sk! (x k) #:prefab)
           (struct primop (which) #:prefab)
           (mk-op-struct ifk (t e ρ k δ) (t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (x xs es e ρ k δ) (x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (l n es vs ρ k δ) (l n es vs ρ-op ... k δ-op ...))
           (mk-op-struct clos (x e ρ free) (x e ρ-op ... free) #:expander-id clos:)
           (mk-op-struct rlos (x r e ρ free) (x r e ρ-op ... free) #:expander-id rlos:)
           (define (kont? v) (or (ls? v) (lrk? v) (ifk? v) (sk!? v) (mt? v)))

           #,@(if (given touches)
                  #`((mk-touches touches clos: rlos: #,(zero? (attribute K))))
                  #'())
           (splicing-syntax-parameterize ([target-σ? #,σ-threading?]
                                          [target-cs? #,c-passing?])
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
                                                       (add-lib e* r gensym gensym))))])
             (fixpoint step (inj (prepare e))))

           #,@compile-def

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

                  ;; We need this intermediate step so that σ-∆s work.
                  ;; The above join is not merged into the store until
                  ;; after the step, and the address is needed by the call.
                  [(ls: l n '() v-addrs ρ a δ)
                   (define v-addr (make-var-contour (cons l n) δ))
                   (define args (reverse (cons v-addr v-addrs)))
                   (generator
                    (do (co-σ) ([σ*-ls #:join-forcing co-σ v-addr v]
                                [k #:in-get σ*-ls a])
                      (yield (ap σ*-ls l (first args) (rest args) k δ))))]

                  [(ls: l n (list-rest e es) v-addrs ρ a δ)
                   (define v-addr (make-var-contour (cons l n) δ))
                   (generator
                    (do (co-σ) ([σ*-lsn #:join-forcing co-σ v-addr v])
                      (yield (ev σ*-lsn e ρ
                                 (ls l (add1 n) es (cons v-addr v-addrs) ρ a δ) δ))))]
                  [(ifk: t e ρ a δ)
                   (generator
                    (do (co-σ) ([k* #:in-get co-σ a]
                                [v #:in-force co-σ v])
                      (yield (ev co-σ (if v t e) ρ k* δ))))]
                  [(lrk: x '() '() e ρ a δ)
                   (generator
                    (do (co-σ) ([σ*-lrk #:join-forcing co-σ (lookup-env ρ x) v]
                             [k* #:in-get σ*-lrk a])
                      (yield (ev σ*-lrk e ρ k* δ))))]
                  [(lrk: x (cons y xs) (cons e es) b ρ a δ)
                   (generator
                    (do (co-σ) ([σ*-lrkn #:join-forcing co-σ (lookup-env ρ x) v])
                      (yield (ev σ*-lrkn e ρ (lrk y xs es b ρ a δ) δ))))]
                  [(sk! l a)
                   (generator
                    (do (co-σ) ([σ*-sk! #:join-forcing co-σ l v]
                                [k* #:in-get σ*-sk! a])
                      (yield (co σ*-sk! k* (void)))))]
                  [_ (error 'step "Bad continuation ~a" k)])]

               ;; v is not a value here. It is an address.
               [(ap: ap-σ l fn-addr arg-addrs k δ)
                (generator
                 (do (ap-σ) ([f #:in-get ap-σ fn-addr])
                   (match f
                     [(clos: xs e ρ _)
                      (cond [(= (length xs) (length arg-addrs))
                             (do (ap-σ)
                                 ([(ρ* σ*-clos δ*) #:bind ρ ap-σ l δ xs arg-addrs])
                               (yield (ev σ*-clos e ρ* k δ*)))]
                            ;; Yield the same state to signal "stuckness".
                            [else
                             ;;(printf "Arity error on ~a~%" f)
                             (yield (ap ap-σ l fn-addr arg-addrs k δ))])]
                     [(rlos: xs r e ρ _)
                      (cond [(<= (length xs) (length arg-addrs))
                             (do (ap-σ)
                                 ([(ρ* σ*-clos δ*) #:bind-rest ρ ap-σ l δ xs r arg-addrs])
                               (yield (ev σ*-clos e ρ* k δ*)))]
                            ;; Yield the same state to signal "stuckness".
                            [else
                             ;;(printf "Arity error on ~a~%" f)
                             (yield (ap ap-σ l fn-addr arg-addrs k δ))])]
                     [(primop o) (prim-meaning o ap-σ l δ k arg-addrs)]
                     [(? kont? k)
                      ;; continuations only get one argument.
                      (cond [(and (pair? arg-addrs) (null? (cdr arg-addrs)))
                             (do (ap-σ) ([v (delay ap-σ (car arg-addrs))])
                               (yield (co ap-σ k v)))])]
                     [(== ●) (=> fail)
                      (log-debug "implement ●-call")
                      (fail)]
                     [_
                      (log-info "Called non-function ~a" f)
                      (yield (ap ap-σ l fn-addr arg-addrs k δ))])))]

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
