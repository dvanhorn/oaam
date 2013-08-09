#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt" "primitives.rkt" "parse.rkt"
         "notation.rkt" "op-struct.rkt" "do.rkt" "add-lib.rkt"
         (only-in "tcon.rkt" call ret weak-eq^ TCon-deriv^ TCon-deriv@ for*/∧ may must tl M⊥)
         "graph.rkt"
         racket/unit
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax racket/base
                     #;syntax/parse/experimental/template
                     )
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
         (~optional (~seq #:ans ans:id)  ;; name the answer struct to use/provide
                    #:defaults ([ans (generate-temporary #'ans)]))
         (~optional (~seq #:touches touches:id)) ;; Touch relation specialized for clos
         (~optional (~seq #:clos clos:id) #:defaults ([clos (generate-temporary #'clos)]))
         (~optional (~seq #:rlos rlos:id) #:defaults ([rlos (generate-temporary #'rlos)]))
         (~optional (~seq #:blclos blclos:id) #:defaults ([blclos (generate-temporary #'blclos)]))
         (~optional (~seq #:primop primop:id) #:defaults ([primop (generate-temporary #'primop)]))
         (~optional (~seq #:ev ev:id) #:defaults ([ev (generate-temporary #'ev)]))
         (~optional (~seq #:co co:id) #:defaults ([co (generate-temporary #'co)]))
         ;; Analysis strategies flags (requires the right parameters too)
         (~optional (~and #:compiled compiled?))
         (~optional (~and #:collect-compiled collect-hash:id))
         (~optional (~and #:σ-∆s σ-∆s?))
         (~optional (~and #:sparse sparse?))
         ;; Continuation marks incur a representation overhead.
         ;; We allow this feature to be disabled for benchmarking analysis of
         ;; languages that do not have continuation marks.
         (~optional (~seq (~and #:CM CM?) mark-set (~bind [(cm-op 1) (list #'cm)]))
                    #:defaults ([mark-set #'∅]
                                [(cm-op 1) '()]))
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
           (define σ-passing?* (or (given σ-passing?) (given σ-∆s?)))
           (define σ-threading? (and (given wide?) σ-passing?*))
           (define c-passing? (given set-monad?))]
     #:fail-unless (implies (given global-σ?) (given wide?))
     "Cannot globalize narrow stores."
     #:fail-when (and (given collect-hash) (not (given compiled?)))
     "Cannot collect compiled expressions when not compiling."
     #:fail-unless (implies (given σ-∆s?) (given wide?))
     "Store deltas and narrow stores are antithetical."
     #:fail-unless (or (given fixpoint) (given set-monad?))
     "Cannot use a general fixpoint for step function that doesn't return sets."
     #:fail-when (and (given σ-passing?) (given global-σ?))
     "Cannot use store passing with a global store"
     (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                    (if (zero? (attribute K)) #'(() () ()) #'((ρ) (δ) (l)))]
                   [ev: (format-id #'ev "~a:" #'ev)]
                   [co: (format-id #'co "~a:" #'co)]
                   [co? (format-id #'co "~a?" #'co)]
                   [clos? (format-id #'clos "~a?" #'clos)]
                   [rlos? (format-id #'rlos "~a?" #'rlos)]
                   [blclos? (format-id #'blclos "~a?" #'blclos)]
                   [primop: (format-id #'primop "~a:" #'primop)]
                   ;; represent rσ explicitly in all states?
                   [(σ-op ...) (if (given wide?) #'() #'(rσ))]
                   ;; explicitly pass σ/∆ to compiled forms?
                   [(σ-gop ...) (if σ-passing?* #'(gσ) #'())]
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
                   (syntax-parse syn #:literals (ev cc)
                     [(_ ((~and constr:id (~or ev cc)) . args)) (syntax/loc syn (constr . args))]
                     [(_ e:expr) (syntax/loc syn (let ([v e]) 
                                                   #;(printf "yield ~a~%~%" v)
                                                   (yield-meaning v)))]))
             #'(λ (syn)
                   (syntax-parse syn #:literals (ev)
                     [(_ (ev . args)) (syntax/loc syn (begin (ev-state!) (yield-meaning (ev . args))))]
                     [(_ e:expr) (syntax/loc syn (yield-meaning e))]))))
       (define eval ;; what does ev mean?
         (syntax/loc stx
           (match e
             [(var l x)
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) ([v #:in-delay ev-σ (lookup-env ρ x)])
                    (co-after-var-state!)
                    (yield (co ev-σ ev-τ k v)))
                  ;; Needed for strict/compiled, but for lazy this introduces
                  ;; an unnecessary administrative reduction.
                  #;
                  (do (ev-σ) ()
                    (yield (dr ev-σ k (lookup-env ρ x)))))]
             [(datum l d) (λ% (ev-σ ev-τ ρ k δ)
                              (do (ev-σ) () (yield (co ev-σ ev-τ k d))))]
             [(primr l which)
              (define p (primop (compile-primop which)))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) () (yield (co ev-σ ev-τ k p))))]
             [(lam l x e*)
              (define c (compile e*))
              (define fv (free e))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) () (yield (co ev-σ ev-τ k (clos x c ρ fv)))))]
             [(rlm l x r e*)
              (define c (compile e*))
              (define fv (free e))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) () (yield (co ev-σ ev-τ k (rlos x r c ρ fv)))))]
             [(lrc l xs es b)
              (define c (compile (first es)))
              (define cs (map compile (rest es)))
              (define cb (compile b))
              (define x (first xs))
              (define xs* (rest xs))
              (define ss (map (λ _ nothing) xs))
              (λ% (ev-σ ev-τ ρ k δ)
                  (define as (map (λ (x) (make-var-contour x δ)) xs))
                  (define/ρ ρ* (extend* ρ xs as))
                  (do (ev-σ) ([(σ0 a) #:push ev-σ l δ k]
                              [σ*-lrc #:join* σ0 as ss])
                    (yield (ev σ*-lrc ev-τ c ρ* (lrk (marks-of k) x xs* cs cb ρ* a δ) δ))))]
             [(app l e0 es)
              (define c (compile e0))
              (define cs (map compile es))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) ([(σ*-app a) #:push ev-σ l δ k])
                    (yield (ev σ*-app ev-τ c ρ (ls (marks-of k) l 0 cs '() ρ a δ) δ))))]
             [(ife l e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) ([(σ*-ife a) #:push ev-σ l δ k])
                    (yield (ev σ*-ife ev-τ c0 ρ (ifk (marks-of k) c1 c2 ρ a δ) δ))))]
             [(st! l x e*)
              (define c (compile e*))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) ([(σ*-st! a) #:push ev-σ l δ k])
                    (yield (ev σ*-st! ev-τ c ρ (sk! (marks-of k) (lookup-env ρ x) a) δ))))]
             ;; let/cc is easier to add than call/cc since we make yield
             ;; always make co states for primitives.
             [(lcc l x e*)
              (define c (compile e*))
              (λ% (ev-σ ev-τ ρ k δ)
                  (define x-addr (make-var-contour x δ))
                  (define/ρ ρ* (extend ρ x x-addr))
                  (do (ev-σ) ([σ*-lcc #:join ev-σ x-addr (singleton k)])
                    (yield (ev σ*-lcc ev-τ c ρ* k δ))))]
             ;; Forms for stack inspection
             [(grt l R e*)
              (define c (compile e*))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) () (yield (ev ev-σ ev-τ c ρ (grant k R) δ))))]
             [(fal l)
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) () (yield (co ev-σ ev-τ (mt mt-marks) fail))))]
             [(frm l R e*)
              (define c (compile e*))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) () (yield (ev ev-σ ev-τ c ρ (frame k R) δ))))]
             [(tst l R t e*)
              (define c0 (compile t))
              (define c1 (compile e*))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) ()
                    (if (OK^ R k ev-σ)
                        (yield (ev ev-σ ev-τ c0 ρ k δ))
                        (yield (ev ev-σ ev-τ c1 ρ k δ)))))]
             ;; Forms for higher-order contracts
             [(mon l pℓ nℓ cℓ s e*)
              (define c (compile e*))
              (define cs (scon-compile s))
              (define ℓs (list pℓ nℓ cℓ))
              (λ% (ev-σ ev-τ ρ k δ)
                  (do (ev-σ) ([(σ*-mon a) #:push ev-σ l δ k])
                    (yield (cc σ*-mon ev-τ cs ρ Λη ℓs (stmonk (marks-of k) l c ρ ℓs a δ) δ))))]
             [(tmon l pℓ nℓ cℓ s t e*)
              (define c (compile e*))
              (define cs (scon-compile s))
              (define ℓs (list pℓ nℓ cℓ))
              (λ% (ev-σ ev-τ ρ k δ)
                  (define η (make-var-contour `(η . ,l) δ))
                  (define τ*-mon (join ev-τ η (set t)))
                  (do (ev-σ) ([(σ*-mon a) #:push ev-σ l δ k])
                    (yield (cc σ*-mon τ*-mon cs ρ η ℓs (stmonk (marks-of k) l c ρ ℓs a δ) δ))))]
             [_ (error 'eval "Bad expr ~a" e)])))

       ;; Flat contracts have arbitrary expressions in them which need to be compiled.
       (define seval
         (syntax/loc stx
           (match s
             [(consc l ca cd)
              (define cca (scon-compile ca))
              (define ccd (scon-compile cd))
              (λc% (cc-σ cc-τ ρ η ℓs k δ)
                  (do (cc-σ) ([(σ*-consc a) #:push cc-σ l δ k])
                   (yield (cc σ*-consc cc-τ cca ρ η ℓs (cak (marks-of k) η ℓs ccd ρ a δ) δ))))]
             [(andc l c₀ c₁)
              (define cc₀ (scon-compile c₀))
              (define cc₁ (scon-compile c₁))
              (λc% (cc-σ cc-τ ρ η ℓs k δ)
                  (do (cc-σ) ([(σ*-and a) #:push cc-σ l δ k])
                    (yield (cc σ*-and cc-τ cc₀ ρ η ℓs (and0k (marks-of k) η ℓs cc₁ ρ a δ) δ))))]
             [(orc l c₀ c₁)
              (define cc₀ (scon-compile c₀))
              (define cc₁ (scon-compile c₁))
              (λc% (cc-σ cc-τ ρ η ℓs k δ)
                  (do (cc-σ) ([(σ*-or a) #:push cc-σ l δ k])
                    (yield (cc σ*-or cc-τ cc₀ ρ η ℓs (or0k (marks-of k) η ℓs cc₁ ρ a δ) δ))))]
             [(fltc l e)
              (define c (compile e))
              (λc% (cc-σ cc-τ ρ η ℓs k δ)
                  (do (cc-σ) () (yield (ev cc-σ cc-τ c ρ k δ))))]
             [(arrc l name ncs pc)
              (define cncs (map scon-compile ncs))
              (define cpc (scon-compile pc))
              (match cncs
                ['() (λc% (cc-σ cc-τ ρ η ℓs k δ)
                         (do (cc-σ) ([(σ*-dom a) #:push cc-σ l δ k])
                           (yield (cc σ*-dom cc-τ cpc ρ η ℓs (rngk (marks-of k) η ℓs '() cpc name a δ) δ))))]
                [(cons cnc cncs)
                 (λc% (cc-σ cc-τ ρ η ℓs k δ)
                     (do (cc-σ) ([(σ*-dom a) #:push cc-σ l δ k])
                       (yield (cc σ*-dom cc-τ cnc ρ η ℓs (domk (marks-of k) η ℓs cncs '() cpc ρ name a δ) δ))))]
                [_ (error 'arrc "Bad ~a" cncs)])]

             [(or (== anyc eq?) (== nonec eq?))
              (λc% (cc-σ cc-τ ρ η ℓs k δ)
                   (do (cc-σ) () (yield (co cc-σ cc-τ k s))))]
             [_ (error 'eval "Bad contract ~a" s)])))

       (define compile-def
         (cond [(given compiled?)
                (define hidden-σ (and (given σ-∆s?) (not (given global-σ?)) (generate-temporary #'hidden)))
                (with-syntax ([(top ...) (listy hidden-σ)]
                              [topp (or hidden-σ #'gσ)])
                  (quasisyntax/loc stx
                    ((define-syntax-rule (... (λ% (gσ τ ρ k δ) body ...))
                       (λ (top ... σ-gop ... τ ρ-op ... k δ-op ...)
                          (syntax-parameterize ([yield (... (... #,yield-ev))]
                                                [top-σ (make-rename-transformer #'topp)]
                                                [target-σ (make-rename-transformer #'gσ)]
                                                [target-τ (make-rename-transformer #'τ)]
                                                [top-σ? #t])
                            body (... ...))))
                     (define-syntax-rule (... (λc% (gσ τ ρ η ℓs k δ) body ...))
                       (λ (top ... σ-gop ... τ ρ-op ... η ℓs k δ-op ...)
                          (syntax-parameterize ([yield (... (... #,yield-ev))]
                                                [top-σ (make-rename-transformer #'topp)]
                                                [target-σ (make-rename-transformer #'gσ)]
                                                [target-τ (make-rename-transformer #'τ)]
                                                [top-σ? #t])
                            body (... ...))))
                     #,@(if (given collect-hash)
                            (quasisyntax/loc stx
                              ((define (compile e)
                                 (define form #,eval)
                                 (hash-set! collect-hash form e)
                                 form)
                               (define (scon-compile s)
                                 (define form #,seval)
                                 (hash-set! collect-hash form s)
                                 form)))
                            (quasisyntax/loc stx
                              ((define (compile e) #,eval)
                               (define (scon-compile s) #,seval)
                               ))))))]
               [else
                ;; brittle, since other identifiers must be the same in ev: and cc:
                (syntax/loc stx
                  ((... (define-syntax-rule (λ% (ev-σ ev-τ ρ k δ) body ...)
                          (generator body ...)))
                   (... (define-syntax-rule (λc% (cc-σ cc-τ ρ η ℓs k δ) body ...)
                          (generator body ...)))
                   (define compile values)
                   (define scon-compile values)))]))

       (quasisyntax/loc stx
         (begin ;; specialize representation given that 0cfa needs less
           (define scon-ok? (make-parameter #f))
           (mk-op-struct co (rσ τ k v) (σ-op ... τ k v) expander-flags ...)
           ;; Variable dereference causes problems with strict/compiled
           ;; instantiations because store changes are delayed a step.
           ;; We fix this by making variable dereference a new kind of state.
           (mk-op-struct dr (rσ τ k a) (σ-op ... τ k a) expander-flags ...)
           (mk-op-struct chk (rσ τ l vc v res-addr ℓs k δ) (σ-op ... τ l vc v res-addr ℓs k δ-op ...)
                         expander-flags ...)
           (mk-op-struct ans (rσ τ cm v) (σ-op ... τ cm-op ... v) expander-flags ...
                         #:expander-id ans:)
           (mk-op-struct ap (rσ τ l fn-addr v-addrs k δ)
                         (σ-op ... τ l fn-addr v-addrs k δ-op ...)
                         expander-flags ...)
           (mk-op-struct blame (pℓ cℓ msg c v) (pℓ cℓ msg c v))
           ;; Continuation frames
           (mk-op-struct mt (cm) (cm-op ...))
           (mk-op-struct sk! (cm x k) (cm-op ... x k))
           (mk-op-struct ifk (cm t e ρ k δ) (cm-op ... t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (cm x xs es e ρ k δ) (cm-op ... x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (cm l n es vs ρ k δ) (cm-op ... l n es vs ρ-op ... k δ-op ...))
           ;; Keep positive party in case wrapping the value leads to a contract violation.
           (mk-op-struct stmonk (cm l e ρ ℓs k δ) (cm-op ... l e ρ-op ... ℓs k δ-op ...))

           ;; Contract checking continuation frames
           (mk-op-struct chkk (cm v l ℓs k δ) (cm-op ... v l ℓs k δ-op ...))
           (mk-op-struct chkargs (cm l i ℓs nc-todo arg-addrs done-addrs fnv k δ)
                         (cm-op ... l i ℓs nc-todo arg-addrs done-addrs fnv k δ-op ...))
           (mk-op-struct postretk (cm fnv k) (cm-op ... fnv k))
           (mk-op-struct blcons (cm res-addr aa ad k) (cm-op ... res-addr aa ad k))
           (mk-op-struct chkor₀ (cm l ℓs c v res-addr k δ) (cm-op ... l ℓs c v res-addr k δ-op ...))
           (mk-op-struct chkand₀ (cm l ℓs c v res-addr k δ) (cm-op ... l ℓs c v res-addr k δ-op ...))
           (mk-op-struct chkcdr (cm l ℓs res-addr ara ard cd ad k δ) (cm-op ... l ℓs res-addr ara ard cd ad k δ-op ...))
           (mk-op-struct chkflt (cm tempFn tmpArg ℓs k) (cm-op ... tempFn tmpArg ℓs k))

           ;; Contract construction continuation frames
           (mk-op-struct domk (cm η ℓs todo done pos ρ name k δ) (cm-op ... η ℓs todo done pos ρ-op ... name k δ-op ...))
;; mflatt: Add any one of these and get a <local-code> error.
           (mk-op-struct rngk (cm η ℓs ncs pc name k δ) (cm-op ... η ℓs ncs pc name k δ-op ...))
           (mk-op-struct cak (cm η ℓs cd ρ k δ) (cm-op ... η ℓs cd ρ-op ... k δ-op ...))
           (mk-op-struct cdk (cm cv k) (cm-op ... cv k))
           (mk-op-struct and0k (cm η ℓs cc ρ k δ) (cm-op ... η ℓs cc ρ-op ... k δ-op ...))
           (mk-op-struct or0k (cm η ℓs cc ρ k δ) (cm-op ... η ℓs cc ρ-op ... k δ-op ...))
           (mk-op-struct and1k (cm cv k) (cm-op ... cv k))
           (mk-op-struct or1k (cm cv k) (cm-op ... cv k))

           ;; Values
           (struct primop (which) #:prefab)
           (mk-op-struct clos (x e ρ free) (x e ρ-op ... free) #:expander-id clos:)
           (mk-op-struct rlos (x r e ρ free) (x r e ρ-op ... free) #:expander-id rlos:)
           (mk-op-struct blclos (vaddr ncs pc name η ℓs) (vaddr ncs pc name η ℓs) #:expander-id blclos:)

           (define (kont? v) (or (ls? v) (lrk? v) (ifk? v) (sk!? v) (mt? v)
                                 (stmonk? v) (domk? v) (rngk? v) (cak? v) (cdk? v)
                                 (and0k? v) (or0k? v)
                                 (and1k? v) (or1k? v)
                                 (chkk? v) (chkargs? v) (postretk? v) (blcons? v)
                                 (chkor₀? v) (chkand₀? v) (chkcdr? v)))
           ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
           ;; Handling of continuation marks
           (define (marks-of k)
             #,(if (given CM?)
                   #'(match k
                       [(or (mt: cm)
                            (sk!: cm _ _)
                            (ifk: cm _ _ _ _ _)
                            (lrk: cm _ _ _ _ _ _ _)
                            (ls: cm _ _ _ _ _ _ _)
                            (stmonk: cm _ _ _ _ _ _)
                            (domk: cm _ _ _ _ _ _ _ _ _)
                            (rngk: cm _ _ _ _ _ _ _)
                            (cak: cm _ _ _ _ _ _)
                            (cdk: cm _ _)
                            (and0k: cm _ _ _ _ _ _)
                            (or0k: cm _ _ _ _ _ _)
                            (chkk: cm _ _ _ _ _)
                            (chkargs: cm _ _ _ _ _ _ _ _ _)
                            (postretk: cm _ _)
                            (blcons: cm _ _ _ _)
                            (chkor₀: cm _ _ _ _ _ _ _)
                            (chkand₀: cm _ _ _ _ _ _ _)
                            (chkcdr: cm _ _ _ _ _ _ _ _ _)
                            (chkflt: cm _ _ _ _)) cm]
                       [_ (error 'marks-of "Bad cont ~a" k)])
                   #'#f))
           (define (tail-of k)
             #,(if (given CM?)
                   #'(match k
                       [(mt: cm) #f]
                       [(or (sk!: _ _ k)
                            (ifk: _ _ _ _ k _)
                            (lrk: _ _ _ _ _ _ k _)
                            (ls: _ _ _ _ _ _ k _)
                            (stmonk: _ _ _ _ _ k _)
                            (domk: _ _ _ _ _ _ _ _ k _)
                            (rngk: _ _ _ _ _ _ k _)
                            (cak: _ _ _ _ _ k _)
                            (cdk: _ _ k)
                            (and0k: _ _ _ _ _ k _)
                            (or0k: _ _ _ _ _ k _)
                            (chkk: _ _ _ _ k _)
                            (chkargs: _ _ _ _ _ _ _ _ k _)
                            (postretk: _ _ k)
                            (blcons: _ _ _ _ k)
                            (chkor₀: _ _ _ _ _ _ k _)
                            (chkand₀: _ _ _ _ _ _ k _)
                            (chkcdr: _ _ _ _ _ _ _ _ k _)) k]
                       [_ (error 'tail-of "Bad cont ~a" k)])
                   #'#f))
           (define mt-marks
             (for/hash ([permission (in-set mark-set)])
               (values permission 'deny)))
           (define (set-mark cm R)
             (for/fold ([cm* cm]) ([permission (in-set R)])
               (hash-set cm permission 'grant)))
           (define (frame-mark cm R)
             (for/hash ([(permission _) (in-hash cm)])
               (values permission (if (permission . ∈ . R)
                                      'grant
                                      'deny))))

           (define (grant k R)
             #,(if (given CM?)
                   #'(match k
                       [(mt: cm)
                        (mt (set-mark cm R))]
                       [(sk!: cm l k)
                        (sk! (set-mark cm R) l k)]
                       [(ifk: cm t e ρ k δ)
                        (ifk (set-mark cm R) t e ρ k δ)]
                       [(lrk: cm x xs es e ρ k δ)
                        (lrk (set-mark cm R) x xs es e ρ k δ)]
                       [(ls: cm l n es vs ρ k δ)
                        (ls (set-mark cm R) l n es vs ρ k δ)]
                       [_ (error 'grant "TODO ~a" k)])
                   #'#f))

           (define (frame k R)
             #,(if (given CM?)
                   #'(match k
                       [(mt: cm)
                        (mt (frame-mark cm R))]
                       [(sk!: cm l k)
                        (sk! (frame-mark cm R) l k)]
                       [(ifk: cm t e ρ k δ)
                        (ifk (frame-mark cm R) t e ρ k δ)]
                       [(lrk: cm x xs es e ρ k δ)
                        (lrk (frame-mark cm R) x xs es e ρ k δ)]
                       [(ls: cm l n es vs ρ k δ)
                        (ls (frame-mark cm R) l n es vs ρ k δ)]
                       [_ (error 'frame "TODO ~a" k)])
                   #'#f))

           ;; XXX: does not work with actions
           (define-syntax-rule (OK^ R k σ)
             (let ([seen (make-hasheq)])
               (define (overlap? R m)
                 (not (for/or ([(permission status) (in-hash m)]
                               #:when (eq? status 'deny))
                        (permission . ∈ . R))))
               (let loop ([R R] [k k])
                 (define m (marks-of k))
                 (hash-set! seen k #t)
                 (or (∅? R)
                     (and (overlap? R m)
                          (match (tail-of k)
                            [#f #t]
                            [ka
                             (define R*
                               (for/set ([permission (in-set R)]
                                         #:unless (eq? (hash-ref m permission) 'grant))
                                 permission))
                             ;; OR because we're looking for a single path through the store.
                             (for/or ([k (in-set (getter σ ka))]
                                      #:unless (hash-has-key? seen k))
                               (loop R* k))]))))))
           ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
           ;; End of continuation mark handling

           #,@(if (given touches)
                  #`((mk-touches touches clos: rlos: blclos: list #,(zero? (attribute K))))
                  #'())
           (splicing-syntax-parameterize
            ([target-σ? (and #,σ-threading? 'threading)]
             [target-cs? #,c-passing?]
             [target-actions? #,(given sparse?)])
            (define-syntax do-macro
              (mk-do #,(given σ-∆s?)
                     #,c-passing?
                     #,(given global-σ?)
                     #,(given generators?)))
            (mk-flatten-value flatten-value-fn clos: rlos: blclos: kont?)
            (splicing-syntax-parameterize
             ([do (make-rename-transformer #'do-macro)]
              [flatten-value (make-rename-transformer #'flatten-value-fn)])

             ;; ev is special since it can mean "apply the compiled version" or
             ;; make an actual ev state to later interpret.
             #,@(if (given compiled?)
                    (quasisyntax/loc stx
                      ((define-syntax (ev syn)
                         (syntax-case syn ()
                           ;; gσ only optional if it's global
                           [(_ gσ τ e ρ k δ)
                            #'(e #,@(listy (and (given σ-∆s?) (not (given global-σ?)) #'top-σ))
                                 σ-gop ... τ ρ-op ... k δ-op ...)]))
                       (define-syntax (cc syn)
                         (syntax-case syn ()
                           ;; gσ only optional if it's global
                           [(_ gσ τ sc ρ η ℓs k δ)
                            #'(sc #,@(listy (and (given σ-∆s?) (not (given global-σ?)) #'top-σ))
                                  σ-gop ... τ ρ-op ... η ℓs k δ-op ...)]))
                       (define-match-expander ev: ;; inert, but introduces bindings
                         (syntax-rules () [(_ . args) (list . args)]))
                       (define-match-expander cc:
                         (syntax-rules () [(_ . args) (list . args)]))))
                    (quasisyntax/loc stx
                      ((mk-op-struct ev (rσ τ e ρ k δ) (σ-op ... τ e ρ-op ... k δ-op ...)
                                     expander-flags ...)
                       (mk-op-struct cc (rσ τ sc ρ η ℓs k δ) (σ-op ... τ sc ρ-op ... η ℓs k δ-op ...)
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
               (define τ₀ (hash))
               (generator
                   (do (σ₀) () (yield (ev σ₀ τ₀ (compile e) (hash) (mt mt-marks) '())))))

             (define (aval e #:prepare [prepare #,(if (attribute prep-fn)
                                                      #'prep-fn
                                                      #`(λ (e)
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

             (define-syntax mk-prims (mk-mk-prims #,(given global-σ?) #,σ-passing?*
                                                  #,(given σ-∆s?) #,(given compiled?)
                                                  #,(attribute K)))
             (mk-prims prim-meaning compile-primop co clos? rlos? blclos? prim-eq)

             (define (step-event ð τ η event)
               (if (eq? η Λη)
                   (values τ #f)
                   (let-values ([(stepped-ts cause-blame?)
                                 (for/fold ([ts* ∅] [cause-blame? #f])
                                     ([T (in-set (hash-ref τ η (λ () (error 'step "Unbound η ~a" η))))])
                                   (match (ð event T)
                                     [(== M⊥ eq?) (values ts* #t)]
                                     [(tl T* t)
                                      (values (set-add ts* T*) (or cause-blame? (eq? t may)))]))])
                     (values (hash-set τ η stepped-ts)
                             (if (set-empty? stepped-ts)
                                 must
                                 cause-blame?))))) ;; may or #f
             
             (define-syntax-rule (blamer wrap σ cause-blame? good bad)
               (cond
                [(eq? cause-blame? must) (wrap (bad))]
                [(eq? cause-blame? may)
                 (wrap
                     (do (σ) ([g/b (in-list (list #t #f))])
                       (if g/b (good) (bad))))]
                [else (wrap (good))]))

             (define (-matchℓ? v ℓ) (match v
                                     [(blclos: _ _ _ (== ℓ eq?) _ _) #t]
                                     [_ #f]))
            
             (define-syntax (import-ð stx)
               (syntax-case stx ()
                 [(_ σ)
                  #`(begin
                      (define-unit weak-eq@
                        (import) (export weak-eq^)
                        (define (≃ v0 v1)
                          (for*/∧ ([v0 (in-set (force σ v0))]
                                   [v1 (in-set (force σ v1))])
                                  (prim-eq σ v0 v1)))
                        (define matchℓ? -matchℓ?))
                      (define-values/invoke-unit/infer
                        (export #,(syntax-local-introduce #'TCon-deriv^))
                        (link weak-eq@ TCon-deriv@)))]))
             ;; [Rel State State]
             (define (step state)
               (match state
                 ;; Only for compiled/strict
                 #;
                 [(dr: dr-σ k a)
                 (generator
                 (do (dr-σ) ([v #:in-delay dr-σ a]) (yield (co dr-σ k v))))]
                 [(co: co-σ co-τ k v)
                  (import-ð co-σ)
                  (match k
                    [(mt: cm) (generator (do (co-σ) ([v #:in-force co-σ v])
                                           (yield (ans co-σ co-τ cm v))))]

                    ;; We need this intermediate step so that σ-∆s work.
                    ;; The above join is not merged into the store until
                    ;; after the step, and the address is needed by the call.
                    [(ls: cm l n '() v-addrs ρ a δ)
                     (define v-addr (make-var-contour (cons l n) δ))
                     (define args (reverse (cons v-addr v-addrs)))
                     (generator
                         (do (co-σ) ([σ*-ls #:join-forcing co-σ v-addr v]
                                     [k #:in-get σ*-ls a])
                           (yield (ap σ*-ls co-τ l (first args) (rest args) k δ))))]

                    [(ls: cm l n (list-rest e es) v-addrs ρ a δ)
                     (define v-addr (make-var-contour (cons l n) δ))
                     (generator
                         (do (co-σ) ([σ*-lsn #:join-forcing co-σ v-addr v])
                           (yield (ev σ*-lsn co-τ e ρ
                                      (ls cm l (add1 n) es (cons v-addr v-addrs) ρ a δ) δ))))]
                    [(ifk: cm t e ρ a δ)
                     (generator
                         (do (co-σ) ([k* #:in-get co-σ a]
                                     [v #:in-force co-σ v])
                           (yield (ev co-σ co-τ (if v t e) ρ k* δ))))]
                    [(lrk: cm x '() '() e ρ a δ)
                     (generator
                         (do (co-σ) ([σ*-lrk #:join-forcing co-σ (lookup-env ρ x) v]
                                     [k* #:in-get σ*-lrk a])
                           (yield (ev σ*-lrk co-τ e ρ k* δ))))]
                    [(lrk: cm x (cons y xs) (cons e es) b ρ a δ)
                     (generator
                         (do (co-σ) ([σ*-lrkn #:join-forcing co-σ (lookup-env ρ x) v])
                           (yield (ev σ*-lrkn co-τ e ρ (lrk cm y xs es b ρ a δ) δ))))]
                    [(sk!: cm l a)
                     (generator
                         (do (co-σ) ([σ*-sk! #:join-forcing co-σ l v]
                                     [k* #:in-get σ*-sk! a])
                           (yield (co σ*-sk! co-τ k* (void)))))]
                    ;; Contract construction
                    [(cak: cm η ℓs ccd ρ a δ)
                     (generator
                         (do (co-σ) () (yield (cc co-σ co-τ ccd ρ η ℓs (cdk cm v a) δ))))]
                    [(cdk: cm va a)
                     (generator
                         (do (co-σ) ([k* #:in-get co-σ a])
                           (yield (co co-σ co-τ k* (ccons va v)))))]
                    [(and0k: cm η ℓs cc₁ ρ a δ)
                     (generator
                         (do (co-σ) () (yield (cc co-σ co-τ cc₁ ρ η ℓs (and1k cm v a) δ))))]
                    [(and1k: cm vl a)
                     (generator
                         (do (co-σ) ([k* #:in-get co-σ a])
                           (yield (co co-σ co-τ k* (cand vl v)))))]
                    [(or0k: cm η ℓs cc₁ ρ a δ)
                     (generator
                         (do (co-σ) () (yield (cc co-σ co-τ cc₁ ρ η ℓs (or1k cm v a) δ))))]
                    [(or1k: cm vl a)
                     (generator
                         (do (co-σ) ([k* #:in-get co-σ a])
                           (yield (co co-σ co-τ k* (cor vl v)))))]
                    [(rngk: cm η ℓs ncs pc name a δ)
                     (generator
                         (do (co-σ) ([k* #:in-get co-σ a])
                           (yield (co co-σ co-τ k* (cblarr ℓs ncs pc name η)))))]
                    [(domk: cm η ℓs ncs-todo ncs-done cpc ρ name a δ)
                     (match ncs-todo
                       ['()
                        (generator
                         (do (co-σ) ()
                           (yield (cc co-σ co-τ cpc ρ η ℓs
                                      (rngk cm η ℓs (reverse (cons v ncs-done)) cpc name a δ) δ))))]
                       [(cons nc ncs-todo)
                        (generator
                         (do (co-σ) ()
                           (yield (cc co-σ co-τ nc ρ η ℓs
                                      (domk cm η ℓs ncs-todo (cons v ncs-done) cpc ρ name a δ) δ))))]
                       [_ (error 'todo "Todo WAT ~a" ncs-todo)])]
                    ;; Contract attachment
                    [(stmonk: cm l e ρ ℓs a δ)
                     (generator
                         (do (co-σ) () (yield (ev co-σ co-τ e ρ (chkk cm v l ℓs a δ) δ))))]
                    ;; Contract checking
                    [(chkk: cm vc l ℓs a δ)
                     (define res-addr (make-var-contour `(res . ,l) δ))
                     (generator
                         (do (co-σ) ([k* #:in-get co-σ a]
                                     [vchk #:in-force co-σ v])
                           (yield (chk co-σ co-τ l vc vchk res-addr ℓs k* δ))))]
                    [(chkand₀: cm l ℓs c₁ v res-addr a δ)
                     (generator
                         (do (co-σ) ([k* #:in-get co-σ a])
                           (yield (chk co-σ co-τ l c₁ v res-addr ℓs k* δ))))]
                    [(chkor₀: cm l ℓs c₁ v res-addr a δ) (error 'todo "or contracts")]
                    [(chkcdr: cm l ℓs res-addr aca acd cd ad a δ)
                     (generator
                         (do (co-σ) ([vd #:in-get co-σ ad])
                           (yield (chk co-σ co-τ l cd vd acd ℓs (blcons cm res-addr aca acd a) δ))))]
                    [(blcons: cm res-addr aca acd a)
                     (generator
                         (do (co-σ) ([σ*-bcons #:join co-σ res-addr (singleton (consv aca acd))]
                                     [k* #:in-get σ*-bcons a])
                           (yield (co σ*-bcons co-τ k* (addr res-addr)))))]
                    [(chkargs: cm l i ℓs '() '() done-addrs (and fnv (blclos: vaddr _ _ _ η (list pℓ _ cℓ))) a δ)
                     (define arg-addrs (reverse done-addrs))
                     (define-syntax-rule (good)
                       (do (co-σ) ()
                         (yield (ap co-σ co-τ l vaddr arg-addrs (postretk cm fnv a) δ))))
                     (define-syntax-rule (bad)
                       (do (co-σ) ()
                         (yield (ans co-σ co-τ cm (blame pℓ cℓ "Timeline ~a violated contract at ~a" η event)))))
                     ;; Finished validating arguments, so send call event.
                     (define event (call fnv (map (λ (a) (getter co-σ a)) arg-addrs)))
                     (define-values (τ* cause-blame?) (step-event ð co-τ η event))
                     (blamer generator co-σ cause-blame? good bad)]
                    [(chkargs: cm l i ℓs (cons nc ncs) (cons arga arg-addrs) done-addrs fnv a δ)
                     (define chkA (make-var-contour `(chk ,i ,l) δ))
                     (generator
                         (do (co-σ) ([argv #:in-get co-σ arga])
                           (yield (chk co-σ co-τ l nc argv chkA ℓs
                                       (chkargs cm l (add1 i) ℓs ncs arg-addrs (cons chkA done-addrs) fnv a δ) δ))))]
                    [(postretk: cm (and fnv (blclos: vaddr ncs pc name η (and ℓs (list pℓ nℓ cℓ)))) a)
                     (define-syntax-rule (bad)
                       (do (co-σ) ()
                         (yield (ans co-σ co-τ cm (blame pℓ cℓ "Timeline ~a violated contract at ~a" η event)))))
                     (define-syntax-rule (good)
                       (do (co-σ) ([k* #:in-get co-σ a]) (yield (co co-σ τ* k* v))))
                     (define event (ret fnv v))
                     (define-values (τ* cause-blame?) (step-event ð co-τ η event))
                     (blamer generator co-σ cause-blame? good bad)]
                    [(chkflt: cm tempFn tmpArg (list pℓ nℓ cℓ) a)
                     (generator
                       (do (co-σ) ([k* #:in-get co-σ a]
                                   [v #:in-force co-σ v])
                         (if v
                             (yield (co co-σ co-τ k* (addr tmpArg)))
                             (yield (ans co-σ co-τ cm (blame pℓ cℓ "Flat contract failed" (getter co-σ tempFn) (getter co-σ tmpArg)))))))]
                    [_ (error 'step "Bad continuation ~a" k)])]

                 [(chk: ch-σ ch-τ l vc v res-addr (and ℓs (list pℓ nℓ cℓ)) k δ)
                  (match vc
                    [(ccons ca cd)
                     (match v
                       [(consv aa ad)
                        (define aca (make-var-contour `(A . ,l) δ))
                        (define acd (make-var-contour `(D . ,l) δ))
                        (generator
                            (do (ch-σ) ([(σ*-consc a) #:push ch-σ l δ k]
                                        [va #:in-get σ*-consc aa])
                              (yield (chk σ*-consc ch-τ l ca va aca ℓs (chkcdr (marks-of k) l ℓs res-addr aca acd cd ad a δ) δ))))]
                       [(or (? cons^?) (? qcons^?)) (error 'todo "contract •")]
                       [_ (generator (do (ch-σ) () (yield (ans ch-σ ch-τ (marks-of k) (blame pℓ cℓ "Not a cons" vc v)))))])]
                    [(== nonec eq?)
                     (generator (do (ch-σ) () (yield (ans ch-σ ch-τ (marks-of k) (blame pℓ cℓ "None" vc v)))))]
                    [(== anyc eq?)
                     (generator
                         (do (ch-σ) ([σ*-any #:join ch-σ res-addr (singleton v)])
                           (yield (co ch-σ ch-τ k (addr res-addr)))))]
                    [(cor c₀ c₁)
                     (generator
                         (do (ch-σ) ([(σ*-or a) #:push ch-σ l δ k])
                           (chk σ*-or ch-τ l c₀ v res-addr ℓs (chkor₀ (marks-of k) l ℓs c₁ v res-addr a δ) δ)))]
                    [(cand c₀ c₁)
                     (generator
                         (do (ch-σ) ([(σ*-and a) #:push ch-σ l δ k])
                           (chk σ*-and ch-τ l c₀ v res-addr ℓs (chkand₀ (marks-of k) l ℓs c₁ v res-addr a δ) δ)))]
                    [(cblarr ℓs′ ncs pc name η)
                     (define (wrap-if-arity= n)
                       (cond
                        [(= (length ncs) n)
                         (define bladdr (make-var-contour `(bl . ,l) δ))
                         (generator
                          (do (ch-σ) ([σ*-bl #:join ch-σ bladdr (singleton v)]
                                      [σ*-bl2 #:join σ*-bl res-addr (singleton (blclos bladdr ncs pc name η ℓs′))])
                            (yield (co σ*-bl2 ch-τ k (addr res-addr)))))]
                        [else (generator
                                  (do (ch-σ) () (yield (ans ch-σ ch-τ (marks-of k) (blame pℓ cℓ "Arity mismatch" vc v)))))]))
                     (match v
                       [(clos: xs _ _ _) (wrap-if-arity= (length xs))]
                       [(blclos: _ ncs′ _ _ _ _) (wrap-if-arity= (length ncs′))]
                       [(primop o) (error 'todo "Wrap primops")]
                       [_ (generator (do (ch-σ) () (yield (ans ch-σ ch-τ (marks-of k) (blame pℓ cℓ "Not a function" vc v)))))])]
                    [_ ;; Must be a flat contract.
                     (define tempFn (make-var-contour `(flt-tmp-fn . ,l) δ))
                     (define ltmpArg (list res-addr))
                     (generator
                       (do (ch-σ) ([σ*-tmp #:join* ch-σ (cons tempFn ltmpArg) (list (singleton vc) (singleton v))]
                                   [(σ*-tmpk a) #:push σ*-tmp l δ k])
                         (yield (ap σ*-tmpk ch-τ l tempFn ltmpArg (chkflt (marks-of k) tempFn res-addr ℓs a) δ))))])]

                 ;; v is not a value here. It is an address.
                 [(ap: ap-σ ap-τ l fn-addr arg-addrs k δ)
                  (import-ð ap-σ)
                  (generator
                      (do (ap-σ) ([f #:in-get ap-σ fn-addr])
                        (match f
                          [(clos: xs e ρ _)
                           (cond [(= (length xs) (length arg-addrs))
                                  (do (ap-σ)
                                      ([(ρ* σ*-clos δ*) #:bind ρ ap-σ l δ xs arg-addrs])
                                    (yield (ev σ*-clos ap-τ e ρ* k δ*)))]
                                 ;; Yield the same state to signal "stuckness".
                                 [else
                                  (log-info "Arity error on ~a at ~a" f l)
                                  (yield (ap ap-σ ap-τ l fn-addr arg-addrs k δ))])]
                          [(rlos: xs r e ρ _)
                           (cond [(<= (length xs) (length arg-addrs))
                                  (do (ap-σ)
                                      ([(ρ* σ*-clos δ*) #:bind-rest ρ ap-σ l δ xs r arg-addrs])
                                    (yield (ev σ*-clos ap-τ e ρ* k δ*)))]
                                 ;; Yield the same state to signal "stuckness".
                                 [else
                                  (log-info "Arity error on ~a at ~a" f l)
                                  (yield (ap ap-σ ap-τ l fn-addr arg-addrs k δ))])]

                          [(blclos: vaddr ncs pc name η (and ℓs (list pℓ _ cℓ)))
                           (define-syntax-rule (bad)
                             (do (ap-σ) () (yield (ans ap-σ ap-τ (marks-of k) (blame pℓ cℓ "Arity mismatch" f arg-addrs)))))
                           (define-syntax-rule (good)
                             (do (ap-σ) ([(σ*-wr a) #:push ap-σ l δ k])
                               (yield (ap σ*-wr ap-τ l vaddr arg-addrs (postretk (marks-of k) f a) δ))))
                           (cond
                            [(null? ncs) ;; unwrap if 0 arguments
                             (cond
                              [(null? arg-addrs)
                               (define event (call f '()))
                               (define-values (τ* cause-blame?) (step-event ð ap-τ η event))
                               (blamer begin ap-σ cause-blame? good bad)]
                              [else (bad)])]
                            ;; Start checking the arguments
                            [(= (length ncs) (length arg-addrs))
                             (define chkA (make-var-contour `(chk 0 ,l) δ))
                             (do (ap-σ) ([(σ*-chkarg a) #:push ap-σ l δ k]
                                         [va #:in-get σ*-chkarg (car arg-addrs)])
                               (yield (chk σ*-chkarg ap-τ l (car ncs) va chkA ℓs
                                           (chkargs (marks-of k) l 1 ℓs (cdr ncs) (cdr arg-addrs) (list chkA) f a δ) δ)))]
                            [else (bad)])]
                          [(primop o) (prim-meaning o ap-σ ap-τ l δ k arg-addrs)]
                          [(? kont? k)
                           ;; continuations only get one argument.
                           (cond [(and (pair? arg-addrs) (null? (cdr arg-addrs)))
                                  (do (ap-σ) ([v #:in-delay ap-σ (car arg-addrs)])
                                    (yield (co ap-σ ap-τ k v)))]
                                 [else
                                  (log-info "Called continuation with wrong number of arguments (~a): ~a at ~a"
                                            (length arg-addrs) k l)
                                  (yield (ap ap-σ ap-τ l fn-addr arg-addrs k δ))])]
                          [(== ●) (=> fail)
                           (log-debug "implement ●-call")
                           (fail)]
                          [_
                           (log-info "Called non-function ~a" f)
                           (yield (ap ap-σ ap-τ l fn-addr arg-addrs k δ))])))]

                 ;; this code is dead when running compiled code.
                 [(ev: ev-σ ev-τ e ρ k δ)
                  #,(if (given compiled?)
                        #'(generator (do (ev-σ) () (yield (ev ev-σ ev-τ e ρ k δ))))
                        eval)]

                 [(cc: cc-σ cc-τ s ρ η ℓs k δ)
                  #,(if (given compiled?)
                        #'(generator (do (cc-σ) () (yield (cc cc-σ cc-τ s ρ η ℓs k δ))))
                        seval)]

                 [(ans: ans-σ ans-τ cm v) (generator (do (ans-σ) () (yield (ans ans-σ ans-τ cm v))))]
                 [_ (error 'step "Bad state ~a" state)]))

             #;
                 (trace step)

                 )))))]))
