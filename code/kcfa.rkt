#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt" "primitives.rkt" "parse.rkt"
         "notation.rkt" "op-struct.rkt" "do.rkt" "add-lib.rkt"
         (only-in "tcon.rkt" call ret weak-eq^ TCon-deriv^ TCon-deriv@ for*/∧ may must ⊕ tl M⊥)
         "graph.rkt"
         racket/unit
         racket/generic
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax racket/base
                     "notation.rkt"
                     #;syntax/parse/experimental/template
                     )
         racket/stxparam racket/splicing
         racket/trace)
(provide yield-meaning #;<-reprovide
         mk-analysis)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

(define free/l (union-map free))
(define (free-w/o-vars es vars) ((free/l es) . ∖/l . vars))
(struct compiled-w/free (fn v) #:transparent
        #:property prop:procedure (struct-field-index fn)
        #:methods gen:binds-variables
        [(define/generic gfree-box free-box)
         (define/generic gfree free)
         (define (free-box e) (gfree-box (compiled-w/free-v e)))
         (define (free e #:bound [bound ∅]) (gfree (compiled-w/free-v e) #:bound bound))])

(define-syntax (mk-analysis stx)
  (syntax-parse stx
    [(_ (~or ;; analysis parameters
         (~optional (~seq #:fixpoint fixpoint:expr)
                    #:defaults ([fixpoint #'fix]))
         (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
         ;; Touch relation specialized for clos
         (~optional (~seq #:touches touches:id) #:defaults ([touches (generate-temporary #'touchs)]))
         ;; Root addresses for states
         (~optional (~seq #:root root:id) #:defaults ([root (generate-temporary #'root)]))
         (~optional (~seq #:state-base state-base:id) #:defaults ([state-base (generate-temporary #'state-base)]))
         ;; State constructors
         (~optional (~seq #:ans ans:id) #:defaults ([ans (generate-temporary #'ans)]))
         (~optional (~seq #:dr dr:id) #:defaults ([dr (generate-temporary #'dr)]))
         (~optional (~seq #:ev ev:id) #:defaults ([ev (generate-temporary #'ev)]))
         (~optional (~seq #:co co:id) #:defaults ([co (generate-temporary #'co)]))
         (~optional (~seq #:cc cc:id) #:defaults ([cc (generate-temporary #'cc)]))
         (~optional (~seq #:chk chk:id) #:defaults ([chk (generate-temporary #'chk)]))
         (~optional (~seq #:ap ap:id) #:defaults ([ap (generate-temporary #'ap)]))
         ;; Value constructors
         (~optional (~seq #:clos clos:id) #:defaults ([clos (generate-temporary #'clos)]))
         (~optional (~seq #:rlos rlos:id) #:defaults ([rlos (generate-temporary #'rlos)]))
         (~optional (~seq #:blclos blclos:id) #:defaults ([blclos (generate-temporary #'blclos)]))
         (~optional (~seq #:primop primop:id) #:defaults ([primop (generate-temporary #'primop)]))
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
           (define μ? (syntax-parameter-value #'abs-count?))
           (define σ-passing?* (or (given σ-passing?) (given σ-∆s?)))
           (define σ-threading? (and (given wide?) σ-passing?*))
           (define c-passing? (given set-monad?))]
     #:fail-unless (implies (given global-σ?) (given wide?))
     "Cannot globalize narrow stores."
     #:fail-when (and (given collect-hash) (not (given compiled?)))
     "Cannot collect compiled expressions when not compiling."
     #:fail-unless (or (given fixpoint) (given set-monad?))
     "Cannot use a general fixpoint for step function that doesn't return sets."
     #:fail-when (and (given σ-passing?) (given global-σ?))
     "Cannot use store passing with a global store"
     (define (colonize lst)
       (map (λ (x) (format-id x "~a:" x)) (syntax->list lst)))
     (define-syntax if0
       (syntax-rules ()
         [(_ t) (if (eq? 0 (attribute K))
                    (list t)
                    '())]
         [(_ t e) (if (eq? 0 (attribute K))
                      t
                      e)]))
     (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                    (if (zero? (attribute K)) #'(() () ()) #'((ρ) (δ) (l)))]
                   ;; INVARIANT: All instances of mk-abs will use a global μ if widened.
                   [((μ-op ...) (target-μ-op ...))
                    (if (and μ? (not (given wide?)))
                        #'((μ) (target-μ))
                        #'(() ()))]
                   [(ev: co: ans: ap: cc: chk:)
                    (colonize #'(ev co ans ap cc chk))]
                   [co? (format-id #'co "~a?" #'co)]
                   [clos? (format-id #'clos "~a?" #'clos)]
                   [rlos? (format-id #'rlos "~a?" #'rlos)]
                   [blclos? (format-id #'blclos "~a?" #'blclos)]
                   [primop: (format-id #'primop "~a:" #'primop)]
                   [primop? (format-id #'primop "~a?" #'primop)]
                   ;; represent rσ explicitly in all states?
                   [((σ-op ...) (target-σ-op ...))
                    (if (given wide?)
                        #'(() ())
                        #'((rσ) (target-σ)))]
                   ;; explicitly pass σ/∆ to compiled forms?
                   [(σ-gop ...) (if σ-passing?* #'(gσ) #'())]
                   ;; If rσ not part of state and not global, it is passed
                   ;; in as (cons rσ state), so expand accordingly.
                   [(expander-flags ...)
                    (append
                     (cond [(and (given wide?) (not (given global-σ?)))
                            '(#:expander #:with-first-cons)]
                           [else '()]))]
                   [inj-σ (if (given σ-∆s?) #''() #'(hash))])
       (define yield-ev
         (if (attribute compiled?)
             #'(λ (syn)
                  (syntax-parse syn #:literals (ev cc)
                                [(_ ((~and constr:id (~or ev cc)) . args))
                                 (syntax/loc syn (constr . args))]
                                [(_ e:expr)
                                 (quasisyntax/loc syn (yield-meaning e))]))
             #'(λ (syn)
                  (syntax-parse syn #:literals (ev)
                                [(_ (ev . args))
                                 (syntax/loc syn (begin (ev-state!) (yield-meaning (ev . args))))]
                                [(_ e:expr) (syntax/loc syn (yield-meaning e))]))))
       (define eval ;; what does ev mean?
         (syntax/loc stx
           (match e
             [(var l _ x)
              (λ% e (ρ k δ)
                  (do ([v #:in-delay (lookup-env ρ x)])
                      (co-after-var-state!)
                    (yield (co k v)))
                  ;; Needed for strict/compiled, but for lazy this introduces
                  ;; an unnecessary administrative reduction.
                  #;
                  (do ()
                  (yield (dr target-σ target-μ k (lookup-env ρ x)))))]
              [(datum l _ d) (λ% e (ρ k δ)
                                 (do () (yield (co k d))))]
              [(primr l _ which)
               (define p (primop (compile-primop which)))
               (λ% e (ρ k δ)
                   (do () (yield (co k p))))]
              [(lam l _ x e*)
               (define c (compile e*))
               (define fv (free e))
               (λ% e (ρ k δ)
                   (do () (yield (co k (clos x c ρ fv)))))]
              [(rlm l _ x r e*)
               (define c (compile e*))
               (define fv (free e))
               (λ% e (ρ k δ)
                   (do () (yield (co k (rlos x r c ρ fv)))))]
              [(lrc l _ xs es b)
               (define c (compile (first es)))
               (define cs (map compile (rest es)))
               (define cb (compile b))
               (define x (first xs))
               (define xs* (rest xs))
               (define ss (map (λ _ nothing) xs))
               (λ% e (ρ k δ)
                   (define as (map (λ (x) (make-var-contour x δ)) xs))
                   (define/ρ ρ* (extend* ρ xs as))
                   (do ([a #:push l δ k]
                        [#:join* as ss])
                       (yield (ev c ρ* (lrk (marks-of k) x xs* cs cb ρ* a δ) δ))))]
              [(app l _ lchk e0 es)
               (define c (compile e0))
               (define cs (map compile es))
               (λ% e (ρ k δ)
                   (do ([a #:push l δ k])
                       (yield (ev c ρ (ls (marks-of k) l lchk 0 cs '() ρ a δ) δ))))]
              [(ife l _ e0 e1 e2)
               (define c0 (compile e0))
               (define c1 (compile e1))
               (define c2 (compile e2))
               (λ% e (ρ k δ)
                   (do ([a #:push l δ k])
                       (yield (ev c0 ρ (ifk (marks-of k) c1 c2 ρ a δ) δ))))]
              [(st! l _ x e*)
               (define c (compile e*))
               (λ% e (ρ k δ)
                   (do ([a #:push l δ k])
                       (yield (ev c ρ (sk! (marks-of k) (lookup-env ρ x) a) δ))))]
              ;; let/cc is easier to add than call/cc since we make yield
              ;; always make co states for primitives.
              [(lcc l _ x e*)
               (define c (compile e*))
               (λ% e (ρ k δ)
                   (define x-addr (make-var-contour x δ))
                   (define/ρ ρ* (extend ρ x x-addr))
                   (do ([#:join x-addr (singleton k)])
                       (yield (ev c ρ* k δ))))]
              ;; Forms for stack inspection
              [(grt l _ R e*)
               (define c (compile e*))
               (λ% e (ρ k δ)
                   (do () (yield (ev c ρ (grant k R) δ))))]
              [(fal l _)
               (λ% e (ρ k δ)
                   (do () (yield (co (mt mt-marks) fail))))]
              [(frm l _ R e*)
               (define c (compile e*))
               (λ% e (ρ k δ)
                   (do () (yield (ev c ρ (frame k R) δ))))]
              [(tst l _ R t e*)
               (define c0 (compile t))
               (define c1 (compile e*))
               (λ% e (ρ k δ)
                   (do ()
                       (if (OK^ R k)
                           (yield (ev c0 ρ k δ))
                           (yield (ev c1 ρ k δ)))))]
              ;; Forms for higher-order contracts
              [(mon l _ lchk pℓ nℓ cℓ s e*)
               (define c (compile e*))
               (define cs (scon-compile s))
               (define ℓs (list pℓ nℓ cℓ))
               (λ% e (ρ k δ)
                   (do ([a #:push l δ k])
                       (yield (cc cs ρ Λη ℓs (stmonk (marks-of k) l lchk c ρ ℓs a δ) δ))))]
              [(tmon l _ lchk pℓ nℓ cℓ s t e*)
               (define c (compile e*))
               (define cs (scon-compile s))
               (define ℓs (list pℓ nℓ cℓ))
               (λ% e (ρ k δ)
                   (define η (make-var-contour `(η . ,l) δ))
                   (do ([a #:push l δ k]
                        [#:τ-join η (set t)])
                       (yield (cc cs ρ η ℓs (stmonk (marks-of k) l lchk c ρ ℓs a δ) δ))))]
              [_ (error 'eval "Bad expr ~a" e)])))

       ;; Flat contracts have arbitrary expressions in them which need to be compiled.
         (define seval
           (syntax/loc stx
             (match s
               [(consc l _ ca cd)
                (define cca (scon-compile ca))
                (define ccd (scon-compile cd))
                (λc% s (ρ η ℓs k δ)
                     (do ([a #:push l δ k])
                         (yield (cc cca ρ η ℓs (cak (marks-of k) η ℓs ccd ρ a δ) δ))))]
               [(andc l _ c₀ c₁)
                (define cc₀ (scon-compile c₀))
                (define cc₁ (scon-compile c₁))
                (λc% s (ρ η ℓs k δ)
                     (do ([a #:push l δ k])
                         (yield (cc cc₀ ρ η ℓs (and0k (marks-of k) η ℓs cc₁ ρ a δ) δ))))]
               [(orc l _ c₀ c₁)
                (define cc₀ (scon-compile c₀))
                (define cc₁ (scon-compile c₁))
                (λc% s (ρ η ℓs k δ)
                     (do ([a #:push l δ k])
                         (yield (cc cc₀ ρ η ℓs (or0k (marks-of k) η ℓs cc₁ ρ a δ) δ))))]
               [(fltc l _ e)
                (define c (compile e))
                (λc% s (ρ η ℓs k δ)
                     (do () (yield (ev c ρ k δ))))]
               [(arrc l _ name ncs pc)
                (define cncs (map scon-compile ncs))
                (define cpc (scon-compile pc))
                (match cncs
                  ['() (λc% s (ρ η ℓs k δ)
                            (do ([a #:push l δ k])
                                (yield (cc cpc ρ η ℓs (rngk (marks-of k) η ℓs '() name a δ) δ))))]
                  [(cons cnc cncs)
                   (λc% s (ρ η ℓs k δ)
                        (do ([a #:push l δ k])
                            (yield (cc cnc ρ η ℓs (domk (marks-of k) η ℓs cncs '() cpc ρ name a δ) δ))))]
                  [_ (error 'arrc "Bad ~a" cncs)])]

               [(or (== anyc eq?) (== nonec eq?))
                (λc% s (ρ η ℓs k δ)
                     (do () (yield (co k s))))]
               [_ (error 'eval "Bad contract ~a" s)])))

         (define compile-def
           (cond [(given compiled?)
                  (define hidden-σ (and (given σ-∆s?) (not (given global-σ?)) (generate-temporary #'hidden)))
                  (with-syntax ([(top ...) (listy hidden-σ)]
                                [topp (or hidden-σ #'gσ)])
                    (quasisyntax/loc stx
                      ((define-syntax-rule (... (λ% e-omg-capture (ρ k δ) body ...))
                         (compiled-w/free
                          (λ (top ... σ-gop ... μ-op ... τ ρ-op ... k δ-op ...)
                             (syntax-parameterize ([yield (... (... #,yield-ev))]
                                                   [top-σ (make-rename-transformer #'topp)]
                                                   [target-σ (make-rename-transformer #'gσ)]
                                                   [target-μ (make-rename-transformer #'μ)]
                                                   [target-τ (make-rename-transformer #'τ)]
                                                   [top-σ? #t])
                               body (... ...)))
                          e-omg-capture))
                       (define-syntax-rule (... (λc% s-omg-capture (ρ η ℓs k δ) body ...))
                         (compiled-w/free
                          (λ (top ... σ-gop ... μ-op ... τ ρ-op ... η ℓs k δ-op ...)
                             (syntax-parameterize ([yield (... (... #,yield-ev))]
                                                   [top-σ (make-rename-transformer #'topp)]
                                                   [target-σ (make-rename-transformer #'gσ)]
                                                   [target-μ (make-rename-transformer #'μ)]
                                                   [target-τ (make-rename-transformer #'τ)]
                                                   [top-σ? #t])
                               body (... ...)))
                          s-omg-capture))
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
                    ((... (define-syntax-rule (λ% e (ρ k δ) body ...)
                            (generator body ...)))
                     (... (define-syntax-rule (λc% s (ρ η ℓs k δ) body ...)
                            (generator body ...)))
                     (define compile values)
                     (define scon-compile values)))]))

         (quasisyntax/loc stx
           (begin ;; specialize representation given that 0cfa needs less
             (mk-op-struct state-base (rσ μ τ) (σ-op ... μ-op ... τ) expander-flags ...
                           #:implicit ([rσ target-σ] [μ target-μ] [τ target-τ]))
             (mk-op-struct co state-base (k v) (k v) expander-flags ...)
             ;; Variable dereference causes problems with strict/compiled
             ;; instantiations because store changes are delayed a step.
             ;; We fix this by making variable dereference a new kind of state.
             (mk-op-struct dr state-base (k a) (k a) expander-flags ...)
             (mk-op-struct chk state-base (l lchk vc v res-addr ℓs k δ) (l lchk vc v res-addr ℓs k δ-op ...)
                           expander-flags ...)
             (mk-op-struct ans state-base (cm v) (cm-op ... v) expander-flags ...)
             (mk-op-struct ap state-base (l lchk fn-addr v-addrs k δ)
                           (l lchk fn-addr v-addrs k δ-op ...)
                           expander-flags ...)
             (mk-op-struct blame (pℓ cℓ msg c v) (pℓ cℓ msg c v))
             ;; Continuation frames
             (mk-op-struct mt (cm) (cm-op ...))
             (mk-op-struct sk! (cm a k) (cm-op ... a k))
             (mk-op-struct ifk (cm t e ρ k δ) (cm-op ... t e ρ-op ... k δ-op ...))
             (mk-op-struct lrk (cm x xs es e ρ k δ) (cm-op ... x xs es e ρ-op ... k δ-op ...))
             (mk-op-struct ls (cm l lchk n es vs ρ k δ) (cm-op ... l lchk n es vs ρ-op ... k δ-op ...))
             ;; Keep positive party in case wrapping the value leads to a contract violation.
             (mk-op-struct stmonk (cm l lchk e ρ ℓs k δ) (cm-op ... l lchk e ρ-op ... ℓs k δ-op ...))

             ;; Contract checking continuation frames
             (mk-op-struct chkk (cm v l lchk ℓs k δ) (cm-op ... v l lchk ℓs k δ-op ...))
             (mk-op-struct chkargs (cm l lchk i ℓs nc-todo arg-addrs done-addrs fnv k δ)
                           (cm-op ... l lchk i ℓs nc-todo arg-addrs done-addrs fnv k δ-op ...))
             (mk-op-struct postretk (cm l lchk fnv k δ) (cm-op ... l lchk fnv k δ-op ...))
             (mk-op-struct retk (cm a k) (cm-op ... a k))
             (mk-op-struct blcons (cm res-addr aa ad k) (cm-op ... res-addr aa ad k))
             (mk-op-struct chkor₀ (cm l lchk ℓs c v res-addr k δ) (cm-op ... l lchk ℓs c v res-addr k δ-op ...))
             (mk-op-struct chkand₀ (cm l lchk ℓs c v res-addr k δ) (cm-op ... l lchk ℓs c v res-addr k δ-op ...))
             (mk-op-struct chkcdr (cm l lchk ℓs res-addr ara ard cd ad k δ) (cm-op ... l lchk ℓs res-addr ara ard cd ad k δ-op ...))
             (mk-op-struct chkflt (cm tempFn tmpArg ℓs k) (cm-op ... tempFn tmpArg ℓs k))

             ;; Contract construction continuation frames
             (mk-op-struct domk (cm η ℓs todo done pos ρ name k δ) (cm-op ... η ℓs todo done pos ρ-op ... name k δ-op ...))
             (mk-op-struct rngk (cm η ℓs ncs name k δ) (cm-op ... η ℓs ncs name k δ-op ...))
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
                                   (chkk? v) (chkargs? v) (postretk? v) (retk? v) (blcons? v)
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
                              (ls: cm _ _ _ _ _ _ _ _)
                              (stmonk: cm _ _ _ _ _ _ _)
                              (domk: cm _ _ _ _ _ _ _ _ _)
                              (rngk: cm _ _ _ _ _ _)
                              (cak: cm _ _ _ _ _ _)
                              (cdk: cm _ _)
                              (and0k: cm _ _ _ _ _ _)
                              (or0k: cm _ _ _ _ _ _)
                              (chkk: cm _ _ _ _ _ _)
                              (chkargs: cm _ _ _ _ _ _ _ _ _ _)
                              (postretk: cm _ _ _ _ _)
                              (retk: cm _ _)
                              (blcons: cm _ _ _ _)
                              (chkor₀: cm _ _ _ _ _ _ _ _)
                              (chkand₀: cm _ _ _ _ _ _ _ _)
                              (chkcdr: cm _ _ _ _ _ _ _ _ _ _)
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
                              (ls: _ _ _ _ _ _ _ k _)
                              (stmonk: _ _ _ _ _ _ k _)
                              (domk: _ _ _ _ _ _ _ _ k _)
                              (rngk: _ _ _ _ _ k _)
                              (cak: _ _ _ _ _ k _)
                              (cdk: _ _ k)
                              (and0k: _ _ _ _ _ k _)
                              (or0k: _ _ _ _ _ k _)
                              (chkk: _ _ _ _ _ k _)
                              (chkargs: _ _ _ _ _ _ _ _ _ k _)
                              (postretk: _ _ _ k _)
                              (retk: _ _ k)
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
                         [(sk!: cm a k)
                          (sk! (set-mark cm R) a k)]
                         [(ifk: cm t e ρ k δ)
                          (ifk (set-mark cm R) t e ρ k δ)]
                         [(lrk: cm x xs es e ρ k δ)
                          (lrk (set-mark cm R) x xs es e ρ k δ)]
                         [(ls: cm l lchk n es vs ρ k δ)
                          (ls (set-mark cm R) l lchk n es vs ρ k δ)]
                         [_ (error 'grant "TODO ~a" k)])
                     #'#f))

             (define (frame k R)
               #,(if (given CM?)
                     #'(match k
                         [(mt: cm)
                          (mt (frame-mark cm R))]
                         [(sk!: cm a k)
                          (sk! (frame-mark cm R) a k)]
                         [(ifk: cm t e ρ k δ)
                          (ifk (frame-mark cm R) t e ρ k δ)]
                         [(lrk: cm x xs es e ρ k δ)
                          (lrk (frame-mark cm R) x xs es e ρ k δ)]
                         [(ls: cm l lchk n es vs ρ k δ)
                          (ls (frame-mark cm R) l lchk n es vs ρ k δ)]
                         [_ (error 'frame "TODO ~a" k)])
                     #'#f))

             ;; XXX: does not work with actions
             (define-syntax-rule (OK^ R k)
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
                               (for/or ([k (in-set (getter ka))]
                                        #:unless (hash-has-key? seen k))
                                 (loop R* k))]))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
             ;; End of continuation mark handling

             (define (touches v)
               (match v
                 [(or (clos: xs e ρ fvs)
                      (rlos: xs _ e ρ fvs))
                  (touches-ρ ρ #:fvs fvs)]
                 [(blclos: vaddr ncs pc _ η _)
                  (∪ (for/union #:initial (set vaddr η) ([nc (in-list ncs)]) (touches nc))
                     (touches pc))]
                 [(or (ccons ca cd)
                      (cand ca cd)
                      (cor ca cd))
                  (∪ (touches ca) (touches cd))]
                 [(consv a d) (set a d)]
                 [(or (vectorv _ l)
                      (vectorv-immutable _ l)) (list->set l)]
                 [(or (vectorv^ _ a)
                      (vectorv-immutable^ _ a)) (set a)]
                 [(? set? s) (for/union ([v (in-set s)]) (touches v))]
                 [(addr a) (set a)]
                 [_ ∅]))
             
             (define (touches-con c)
               (match c
                 [(or (ccons c₀ c₁)
                      (cand c₀ c₁)
                      (cor c₀ c₁)) (∪ (touches-con c₀) (touches-con c₁))]
                 [(cblarr _ ncs pc _ η)
                  (for/union #:initial (∪1 (touches-con pc) η) ([nc (in-list ncs)])
                             (touches-con nc))]
                 [v (touches v)])) ;; must be a flat contract

             (define-syntax (touches-ρ syn)
               (syntax-parse syn
                 [(_ ρ (~or (~optional (~seq #:variables vars) #:defaults ([vars #''()]))
                            (~optional (~seq #:fvs fvs))
                            (~optional (~and #:many many?))) (... ...)
                            (~optional (~seq e (... ...) es)))
                  #:fail-unless (iff (attribute fvs) (not (or (attribute e) (attribute es))))
                  "Must supply either (exclusively) free variables or values containing free variables"
                  (with-syntax ([es* (cond
                                      [(attribute fvs) #'ignore]
                                      [(not (or (null? (syntax->list #'(e (... ...))))
                                                (attribute many?)))
                                       #'(list e (... ...) es)]
                                      [(attribute many?) #'(list* e (... ...) es)]
                                      [else #'es])])
                    (#,#'quasisyntax
                     (let ([fvs* (#,#'unsyntax
                                  (cond [(attribute fvs) #'fvs]
                                        [(eq? #'es #'es*)
                                         (if (attribute vars)
                                             #'((free es) . ∖/l . vars)
                                             #'(free es))]
                                        [(attribute vars) #'(free-w/o-vars es* vars) ]
                                        [else #'(free/l es*)]))])
                       #,(if0 #'fvs* #`(restrict-to-set ρ fvs*)))))]))
             (define touches/l (union-map touches))
             (define touches-con/l (union-map touches-con))
             (define (touches-κ κ)
               (match κ
                 [(mt: cm) ∅]
                 [(sk!: cm a k) (∪1 (touches-κ k) a)]
                 [(ifk: cm t e ρ k δ) (∪ (touches-κ k) (touches-ρ ρ t e))]
                 [(lrk: cm x xs es e ρ k δ)
                  (∪ (touches-κ k)
                     (touches-ρ ρ (cons e es) #:variables (cons x xs)))]
                 [(ls: cm l lchk n es vs ρ k δ)
                  (∪ (touches-κ k) (touches/l vs) (touches-ρ ρ es))]
                 [(stmonk: cm l lchk e ρ ℓs k δ)
                  (∪ (touches-κ k) (touches-ρ ρ e))]

                 [(chkk: cm v l lchk ℓs k δ)
                  (∪ (touches-κ k) (touches v))]
                 [(chkargs: cm l lchk i ℓs nc-todo arg-addrs done-addrs fnv k δ)
                  (∪/l (∪/l (∪ (touches-κ k) (touches/l nc-todo)) arg-addrs) done-addrs)]
                 [(postretk: cm l lchk fnv k δ) (∪ (touches-κ k) (touches fnv))]
                 [(retk: cm a k) (∪1 (touches-κ k) a)]
                 [(blcons: cm res-addr aa ad k)
                  (∪ (touches-κ k) (set res-addr aa ad))]
                 [(or (chkor₀: cm l lchk ℓs c v res-addr k δ)
                      (chkand₀: cm l lchk ℓs c v res-addr k δ))
                  (∪1 (∪ (touches-κ k) (touches c) (touches v)) res-addr)]
                 [(chkcdr: cm l lchk ℓs res-addr ara ard cd ad k δ)
                  (∪ (touches-κ k) (touches cd) (set res-addr ara ard ad))]
                 [(chkflt: cm tempFn tmpArg ℓs k) (∪1 (∪1 (touches-κ k) tempFn) tmpArg)]

                 [(domk: cm η ℓs todo done pos ρ name k δ)
                  (∪1 (∪ (touches-κ k) (touches-con pos) (touches-con/l done) (touches-ρ ρ todo)))]
                 [(rngk: cm η ℓs ncs name k δ)
                  (∪1 (∪ (touches-κ k) (touches-con/l ncs)) η)]
                 [(cak: cm η ℓs cd ρ k δ)
                  (∪1 (∪ (touches-κ k) (touches-ρ ρ cd)) η)]
                 [(cdk: cm cv k) (∪ (touches-κ k) (touches-con cv))]
                 [(or (or0k: cm η ℓs cc ρ k δ)
                      (and0k: cm η ℓs cc ρ k δ))
                  (∪1 (∪ (touches-κ) (touches-ρ ρ cc)) η)]
                 [(or (and1k: cm cv k)
                      (or1k: cm cv k))
                  (∪ (touches-con cv) (touches-κ k))]))

             (define (root state touches)
               (match state
                 [(co: σ μ τ k v) (∪ (touches-κ k) (touches v))]
                 [(ap: σ μ τ l lchk fn-a arg-addrs k δ)
                  (∪/l (touches-κ k) (cons fn-a arg-addrs))]
                 [(chk: σ μ τ l lchk vc v res-addr ℓs k δ)
                  (∪1 (∪ (touches-κ k) (touches-con vc) (touches v)) res-addr)]
                 [(ans: σ μ τ cm v) (touches v)]
                 [(cc: σ μ τ s ρ η ℓs k δ) (∪1 (∪ (touches k) (touches-ρ ρ s)) η)]
                 [(ev: σ μ τ e ρ k δ) (∪ (touches-κ k) (touches-ρ ρ e))]))

             (splicing-syntax-parameterize
              ([target-σ? (and #,σ-threading? 'threading)]
               [target-cs? #,c-passing?]
               [target-actions? #,(given sparse?)])
              (define-syntax do-macro
                (mk-do #,(given σ-∆s?)
                       #,c-passing?
                       #,(given global-σ?)
                       #,(given generators?)
                       #,μ?))
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
                             [(_ e ρ k δ)
                              #'(e #,@(listy (and (given σ-∆s?) (not (given global-σ?)) #'top-σ))
                                   target-σ-op ...
                                   target-μ-op ...
                                   target-τ ρ-op ... k δ-op ...)]))
                         (define-syntax (cc syn)
                           (syntax-case syn ()
                             ;; gσ only optional if it's global
                             [(_ sc ρ η ℓs k δ)
                              #'(sc #,@(listy (and (given σ-∆s?) (not (given global-σ?)) #'top-σ))
                                    target-σ-op ...
                                    target-μ-op ... target-τ ρ-op ... η ℓs k δ-op ...)]))
                         (define-match-expander ev: ;; inert, but introduces bindings
                           (syntax-rules () [(_ . args) (list . args)]))
                         (define-match-expander cc:
                           (syntax-rules () [(_ . args) (list . args)]))))
                      (quasisyntax/loc stx
                        ((mk-op-struct ev state-base (e ρ k δ) (e ρ-op ... k δ-op ...)
                                       expander-flags ...)
                         (mk-op-struct cc state-base (sc ρ η ℓs k δ) (sc ρ-op ... η ℓs k δ-op ...)
                                       expander-flags ...))))

               (define-syntax-rule (define/ρ ρ body)
                 #,(if0 #'(void)
                        #'(define ρ body)))

               ;; No environments in 0cfa
               (define-syntax-rule (lookup-env ρ x)
                 #,(if0 #'x
                        #'(hash-ref ρ x (λ () (error 'lookup "Unbound var ~a" x)))))
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
                 (define μ₀ (hash))
                 (define τ₀ (hash))
                 (syntax-parameterize ([target-σ (make-rename-transformer #'σ₀)]
                                       [target-μ (make-rename-transformer #'μ₀)]
                                       [target-τ (make-rename-transformer #'τ₀)])
                   (generator
                       (do () (yield (ev (compile e) (hash) (mt mt-marks) '()))))))

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
                                                    #,(given σ-∆s?) #,μ? #,(given compiled?)
                                                    #,(attribute K)))
               (mk-prims prim-meaning compile-primop co clos? rlos? blclos? prim-eq)

               (define (step-event ð τ η single-η? event)
                 (if (eq? η Λη)
                     (values τ #f)
                     (let-values ([(stepped-ts cause-blame?)
                                   (for/fold ([ts* ∅] [cause-blame? #f])
                                       ([T (in-set (hash-ref τ η (λ () (error 'step "Unbound η ~a" η))))])
                                     (match (ð event T)
                                       [(== M⊥ eq?) (values ts* (or cause-blame? must))] ;; must > #f but must < may
                                       [(tl T* t)
                                        (values (set-add ts* T*)
                                                (or (and (eq? may t) t) ;; Jump up to may, if may.
                                                    ;; Otherwise, use whatever else we had.
                                                    cause-blame?))]))])
                       (values (if single-η?
                                   (hash-set τ η stepped-ts)
                                   (hash-union τ η stepped-ts))
                               (if (set-empty? stepped-ts)
                                   must
                                   cause-blame?))))) ;; may or #f

               (define-syntax-rule (blamer wrap cause-blame? good bad)
                 (cond
                  [(eq? cause-blame? must) (wrap (bad))]
                  [(eq? cause-blame? may)
                   (wrap
                    (do ([g/b (in-list (list #t #f))])
                        (if g/b (good) (bad))))]
                  [else (wrap (good))]))

               (define (-matchℓ? v ℓ) (match v
                                        [(blclos: _ _ _ (== ℓ eq?) _ _) #t]
                                        [_ #f]))

               (define-syntax (import-ð stx)
                 (syntax-case stx ()
                   [(_)
                    #`(begin
                        (define-unit weak-eq@
                          (import) (export weak-eq^)
                          (define (≃ v0 v1)
                            (for*/∧ ([v0 (in-set (force v0))]
                                     [v1 (in-set (force v1))])
                                    (prim-eq v0 v1)))
                          (define matchℓ? -matchℓ?))
                        (define-values/invoke-unit/infer
                          (export #,(syntax-local-introduce #'TCon-deriv^))
                          (link weak-eq@ TCon-deriv@)))]))

               ;; [Rel State State]
               (define (step state)
                 (match-state state
                   ;; Only for compiled/strict
                   #;
                   [(dr: dr-σ k a)
                   (generator
                   (do ([v #:in-delay dr-σ a]) (yield (co dr-σ k v))))]
                   [(co: co-σ co-μ co-τ k v)
                    (import-ð)
                    (match k
                      [(mt: cm) (generator (do ([fv #:in-force v])
                                               (yield (ans cm fv))))]

                      ;; We need this intermediate step so that σ-∆s work.
                      ;; The above join is not merged into the store until
                      ;; after the step, and the address is needed by the call.
                      [(ls: cm l lchk n '() v-addrs ρ a δ)
                       (define v-addr (make-var-contour (cons l n) δ))
                       (define args (reverse (cons v-addr v-addrs)))
                       (generator
                           (do ([#:join-forcing v-addr v]
                                [k #:in-get a])
                               (yield (ap l lchk (first args) (rest args) k δ))))]

                      [(ls: cm l lchk n (list-rest e es) v-addrs ρ a δ)
                       (define v-addr (make-var-contour (cons l n) δ))
                       (generator
                           (do ([#:join-forcing v-addr v])
                               (yield (ev e ρ
                                          (ls cm l lchk (add1 n) es (cons v-addr v-addrs) ρ a δ) δ))))]
                      [(ifk: cm t e ρ a δ)
                       (generator
                           (do ([k* #:in-get a]
                                [v #:in-force v])
                               (yield (ev (if v t e) ρ k* δ))))]
                      [(lrk: cm x '() '() e ρ a δ)
                       (generator
                           (do ([#:join-forcing (lookup-env ρ x) v]
                                [k* #:in-get a])
                               (yield (ev e ρ k* δ))))]
                      [(lrk: cm x (cons y xs) (cons e es) b ρ a δ)
                       (generator
                           (do ([#:join-forcing (lookup-env ρ x) v])
                               (yield (ev e ρ (lrk cm y xs es b ρ a δ) δ))))]
                      [(sk!: cm addr a)
                       (generator
                           (do ([#:join-forcing addr v]
                                [k* #:in-get a])
                               (yield (co k* (void)))))]

                      ;; Contract construction
                      [(cak: cm η ℓs ccd ρ a δ) ;; FIXME: what if v is lazy?
                       (generator
                           (do () (yield (cc ccd ρ η ℓs (cdk cm v a) δ))))]
                      [(cdk: cm va a)
                       (generator
                           (do ([k* #:in-get a])
                               (yield (co k* (ccons va v)))))]
                      [(and0k: cm η ℓs cc₁ ρ a δ)
                       (generator
                           (do () (yield (cc cc₁ ρ η ℓs (and1k cm v a) δ))))]
                      [(and1k: cm vl a)
                       (generator
                           (do ([k* #:in-get a])
                               (yield (co k* (cand vl v)))))]
                      [(or0k: cm η ℓs cc₁ ρ a δ)
                       (generator
                           (do () (yield (cc cc₁ ρ η ℓs (or1k cm v a) δ))))]
                      [(or1k: cm vl a)
                       (generator
                           (do ([k* #:in-get a])
                               (yield (co k* (cor vl v)))))]
                      [(rngk: cm η ℓs ncs name a δ)
                       (generator
                           (do ([k* #:in-get a])
                               (yield (co k* (cblarr ℓs ncs v name η)))))]
                      [(domk: cm η ℓs '() ncs-done cpc ρ name a δ)
                       (generator
                           (do ()
                               (yield (cc cpc ρ η ℓs
                                          (rngk cm η ℓs (reverse (cons v ncs-done)) name a δ) δ))))]
                      [(domk: cm η ℓs (cons nc ncs-todo) ncs-done cpc ρ name a δ)
                       (generator
                           (do ()
                               (yield (cc nc ρ η ℓs
                                          (domk cm η ℓs ncs-todo (cons v ncs-done) cpc ρ name a δ) δ))))]

                      ;; Contract attachment
                      [(stmonk: cm l lchk e ρ ℓs a δ)
                       (generator
                           (do () (yield (ev e ρ (chkk cm v l lchk ℓs a δ) δ))))]

                      ;; Contract checking
                      [(chkk: cm vc l lchk ℓs a δ)
                       (define res-addr (make-var-contour `(res . ,lchk) δ))
                       (generator
                           (do ([k* #:in-get a]
                                [vchk #:in-force v])
                               (yield (chk l lchk vc vchk res-addr ℓs k* δ))))]

                      [(chkand₀: cm l lchk ℓs c₁ v res-addr a δ)
                       (generator
                           (do ([k* #:in-get a])
                               (yield (chk l lchk c₁ v res-addr ℓs k* δ))))]
                      [(chkor₀: cm l lchk ℓs c₁ v res-addr a δ) (error 'todo "or contracts")]

                      [(chkcdr: cm l lchk ℓs res-addr aca acd cd ad a δ)
                       (generator
                           (do ([vd #:in-get ad])
                               (yield (chk l lchk cd vd acd ℓs (blcons cm res-addr aca acd a) δ))))]
                      [(blcons: cm res-addr aca acd a)
                       (generator
                           (do ([#:join res-addr (singleton (consv aca acd))]
                                [k* #:in-get a])
                               ;; XXX: res-addr may never have a contract in it!
                               (yield (co k* (addr res-addr)))))]

                      [(chkargs: cm l lchk i ℓs '() '() done-addrs (and fnv (blclos: vaddr _ _ _ η (list pℓ _ cℓ))) a δ)
                       (define arg-addrs (reverse done-addrs))
                       (define-syntax-rule (good)
                         (do ()
                             (ap-after-call-state!)
                           (yield (ap l lchk vaddr arg-addrs (postretk cm l lchk fnv a δ) δ))))
                       (define-syntax-rule (bad)
                         (do ()
                             (yield (ans cm (blame pℓ cℓ "Violated timeline contract at call" η event)))))
                       ;; Finished validating arguments, so send call event.
                       (define event (call fnv (map getter arg-addrs)))
                       (define single-η?
                         #,(if μ? #'(eq? 1 (μgetter η)) #'#f))
                       (define-values (τ* cause-blame?) (step-event ð target-τ η single-η? event))
                       (syntax-parameterize ([target-τ (make-rename-transformer #'τ*)])
                         (blamer generator cause-blame? good bad))]
                      [(chkargs: cm l lchk i ℓs (cons nc ncs) (cons arga arg-addrs) done-addrs fnv a δ)
                       (define chkA (make-var-contour `(chk ,i ,l) δ))
                       (generator
                           (do ([argv #:in-get arga])
                               (yield (chk l lchk nc argv chkA ℓs
                                           (chkargs cm l lchk (add1 i) ℓs ncs arg-addrs (cons chkA done-addrs) fnv a δ) δ))))]

                      [(postretk: cm l lchk (and fnv (blclos: vaddr ncs pc name η (and ℓs (list pℓ nℓ cℓ)))) a δ)
                       (define event (ret fnv (force v)))
                       (define ret-addr (make-var-contour `(ret . ,lchk) δ))
                       (define ret-cont (make-var-contour `(retk . ,lchk) δ))
                       (define-syntax-rule (bad)
                         (do ()
                             (yield (ans cm (blame pℓ cℓ "Violated timeline contract at return" η event)))))
                       (define-syntax-rule (good)
                         (do ([rv #:in-force v])
                             (chk-after-ret-state!)
                           (yield (chk l ret-cont pc rv ret-addr ℓs (retk cm ret-addr a) δ))))
                       (define single-η?
                         #,(if μ? #'(eq? 1 (μgetter η)) #'#f))
                       (define-values (τ* cause-blame?) (step-event ð target-τ η single-η? event))
                       (syntax-parameterize ([target-τ (make-rename-transformer #'τ*)])
                         (blamer generator cause-blame? good bad))]
                      [(retk: cm ret-addr a)
                       (generator
                           (do ([k* #:in-get a]) (yield (co k* (addr ret-addr)))))]

                      [(chkflt: cm tempFn tmpArg (list pℓ nℓ cℓ) a)
                       (generator
                           (do ([k* #:in-get a]
                                [v #:in-force v])
                               (if v ;; contract check successful.
                                   (yield (co k* (addr tmpArg)))
                                   (yield (ans cm (blame pℓ cℓ "Flat contract failed" (getter tempFn) (getter tmpArg)))))))]
                      [_ (error 'step "Bad continuation ~a" k)])]

                   [(chk: ch-σ ch-μ ch-τ l lchk vc v res-addr (and ℓs (list pℓ nℓ cℓ)) k δ)
                    (match vc
                      [(ccons ca cd)
                       (match v
                         [(consv aa ad)
                          (define aca (make-var-contour `(A . ,lchk) δ))
                          (define acd (make-var-contour `(D . ,lchk) δ))
                          (generator
                              (do ([a #:push lchk δ k]
                                   [va #:in-get aa])
                                  (yield (chk l lchk ca va aca ℓs (chkcdr (marks-of k) l lchk ℓs res-addr aca acd cd ad a δ) δ))))]
                         [(or (? cons^?) (? qcons^?)) (error 'todo "contract •")]
                         [_ (generator (do () (yield (ans (marks-of k) (blame pℓ cℓ "Not a cons" vc v)))))])]
                      [(== nonec eq?)
                       (generator (do () (yield (ans (marks-of k) (blame pℓ cℓ "None" vc v)))))]
                      [(== anyc eq?)
                       (generator
                           (do ([#:join res-addr (singleton v)])
                               (yield (co k (addr res-addr)))))]
                      [(cor c₀ c₁)
                       (generator
                           (do ([a #:push lchk δ k])
                               (yield (chk l lchk c₀ v res-addr ℓs (chkor₀ (marks-of k) l lchk ℓs c₁ v res-addr a δ) δ))))]
                      [(cand c₀ c₁)
                       (generator
                           (do ([a #:push lchk δ k])
                               (yield (chk l lchk c₀ v res-addr ℓs (chkand₀ (marks-of k) l lchk ℓs c₁ v res-addr a δ) δ))))]
                      [(cblarr ℓs′ ncs pc name η)
                       (define (wrap-if-arity= n)
                         (cond
                          [(= (length ncs) n)
                           (define bladdr (make-var-contour `(bl . ,lchk) δ))
                           (generator
                               (do ([#:join bladdr (singleton v)]
                                    [#:join res-addr (singleton (blclos bladdr ncs pc name η ℓs′))])
                                   (yield (co k (addr res-addr)))))]
                          [else (generator
                                    (do ()
                                        (yield (ans (marks-of k) (blame pℓ cℓ "Arity mismatch" vc v)))))]))
                       (match v
                         [(clos: xs _ _ _) (wrap-if-arity= (length xs))]
                         [(blclos: _ ncs′ _ _ _ _) (wrap-if-arity= (length ncs′))]
                         [(primop o) (error 'todo "Wrap primops")]
                         [_ (generator (do () (yield (ans (marks-of k) (blame pℓ cℓ "Not a function" vc v)))))])]
                      [(or (? blclos?) (? clos?) (? rlos?) (? primop?)) ;; Must be a flat contract.
                       (define tempFn (make-var-contour `(flt-tmp-fn . ,lchk) δ))
                       (define templ (make-var-contour `(flt-tmp-l . ,lchk) δ))
                       (define tempChk (make-var-contour `(flt-tmp-chk . ,lchk) δ))
                       (define tempChk2 (make-var-contour `(flt-tmp-chk2 . ,lchk) δ))
                       (define ltmpArg (list res-addr))
                       (generator
                           (do ([#:join* (cons tempFn ltmpArg) (list (singleton vc) (singleton v))]
                                [a #:push tempChk δ k])
                               (yield (ap templ tempChk2 tempFn ltmpArg
                                          (chkflt (marks-of k) tempFn res-addr ℓs a) δ))))]
                      [_
                       (log-info "Bad contract to check ~a on ~a" vc v)
                       (generator (do () (yield (chk l lchk vc v res-addr ℓs k δ))))])]

                   ;; v is not a value here. It is an address.
                   [(ap: ap-σ ap-μ ap-τ l lchk fn-addr arg-addrs k δ)
                    (import-ð)
                    (generator
                        (do ([f #:in-get fn-addr])
                            (match f
                              [(clos: xs e ρ _)
                               (cond [(= (length xs) (length arg-addrs))
                                      (do ([(ρ* δ*) #:bind ρ l δ xs arg-addrs])
                                          (yield (ev e ρ* k δ*)))]
                                     ;; Yield the same state to signal "stuckness".
                                     [else
                                      (log-info "Arity error on ~a at ~a" f l)
                                      (yield (ap l lchk fn-addr arg-addrs k δ))])]
                              [(rlos: xs r e ρ _)
                               (cond [(<= (length xs) (length arg-addrs))
                                      (do ([(ρ* δ*) #:bind-rest ρ l δ xs r arg-addrs])
                                          (yield (ev e ρ* k δ*)))]
                                     ;; Yield the same state to signal "stuckness".
                                     [else
                                      (log-info "Arity error on ~a at ~a" f l)
                                      (yield (ap l lchk fn-addr arg-addrs k δ))])]

                              [(blclos: vaddr ncs pc name η (and ℓs (list pℓ nℓ cℓ)))
                               (define-syntax-rule (bad)
                                 (do () (yield (ans (marks-of k) (blame pℓ cℓ "Arity mismatch" f arg-addrs)))))
                               (cond
                                [(null? ncs) ;; unwrap if 0 arguments
                                 (cond
                                  [(null? arg-addrs)
                                   (define-syntax-rule (good)
                                     (do ([a #:push lchk δ k])
                                         (ap-after-call-state!)
                                       (yield (ap l lchk vaddr arg-addrs
                                                  (postretk (marks-of k) l lchk f a δ) δ))))
                                   (define event (call f '()))
                                   (define single-η?
                                     #,(if μ? #'(eq? 1 (μgetter η)) #'#f))
                                   (define-values (τ* cause-blame?) (step-event ð target-τ η single-η? event))
                                   (syntax-parameterize ([target-τ (make-rename-transformer #'τ*)])
                                     (blamer begin cause-blame? good bad))]
                                  [else (bad)])]
                                ;; Start checking the arguments
                                [(= (length ncs) (length arg-addrs))
                                 (define ℓs′ (list nℓ pℓ cℓ)) ;; Swap blame, since we're checking negative party now
                                 (define chkA (make-var-contour `(chk 0 ,l) δ))
                                 (do ([a #:push lchk δ k]
                                      [va #:in-get (car arg-addrs)])
                                     (yield (chk l lchk (car ncs) va chkA ℓs′
                                                 (chkargs (marks-of k) l lchk 1 ℓs′ (cdr ncs) (cdr arg-addrs) (list chkA) f a δ) δ)))]
                                [else (bad)])]

                              [(primop o) (prim-meaning o l δ k arg-addrs)]
                              [(? kont? k)
                               ;; continuations only get one argument.
                               (cond [(and (pair? arg-addrs) (null? (cdr arg-addrs)))
                                      (do ([v #:in-delay (car arg-addrs)])
                                          (yield (co k v)))]
                                     [else
                                      (log-info "Called continuation with wrong number of arguments (~a): ~a at ~a"
                                                (length arg-addrs) k l)
                                      (yield (ap l lchk fn-addr arg-addrs k δ))])]
                              [(== ●) (=> fail)
                               (log-debug "implement ●-call")
                               (fail)]
                              [_
                               (log-info "Called non-function ~a" f)
                               (yield (ap l lchk fn-addr arg-addrs k δ))])))]

                   ;; this code is dead when running compiled code.
                   [(ev: ev-σ ev-μ ev-τ e ρ k δ)
                    #,(if (given compiled?)
                          #'(generator (do () (yield (ev e ρ k δ))))
                          eval)]

                   [(cc: cc-σ cc-μ cc-τ s ρ η ℓs k δ)
                    #,(if (given compiled?)
                          #'(generator (do () (yield (cc s ρ η ℓs k δ))))
                          seval)]

                   [(ans: ans-σ ans-μ ans-τ cm v) (generator (do () (yield (ans cm v))))]
                   [_ (error 'step "Bad state ~a" state)]))

#;
                 (trace step)

                 )))))]))
