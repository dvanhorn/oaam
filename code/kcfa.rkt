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
         mk-analysis
         debug-check)
(define debug-check (make-parameter '()))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

(define-syntax (mk-analysis stx)
  (syntax-parse stx
    [(_ (~or ;; analysis parameters
         (~optional (~seq #:fixpoint fixpoint:expr)
                    #:defaults ([fixpoint #'fix]))
         (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
         ;; Name representations' structs
         (~optional (~seq #:ans ans:id) #:defaults ([ans (generate-temporary #'ans)]))
         (~optional (~seq #:dr dr:id) #:defaults ([dr (generate-temporary #'dr)]))
         (~optional (~seq #:ar ar:id) #:defaults ([ar (generate-temporary #'ar)]))
         (~optional (~seq #:ap ap:id) #:defaults ([ap (generate-temporary #'ap)]))
         (~optional (~seq #:co co:id) #:defaults ([co (generate-temporary #'co)]))
         ;; Continuation frames
         (~optional (~seq #:mt mt:id) #:defaults ([mt (generate-temporary #'mt)]))
         (~optional (~seq #:sk! sk!:id) #:defaults ([sk! (generate-temporary #'sk!)]))
         (~optional (~seq #:ifk ifk:id) #:defaults ([ifk (generate-temporary #'ifk)]))
         (~optional (~seq #:lrk lrk:id) #:defaults ([lrk (generate-temporary #'lrk)]))
         (~optional (~seq #:ls ls:id) #:defaults ([ls (generate-temporary #'ls)]))
         (~optional (~seq #:clos clos:id) #:defaults ([clos (generate-temporary #'clos)]))
         (~optional (~seq #:rlos rlos:id) #:defaults ([rlos (generate-temporary #'rlos)]))
         ;; Integrated analysis information stored in each state
         (~optional (~seq #:extra (extra:id ...)) #:defaults ([(extra 1) '()]))
         ;; Sometimes things get widened.
         (~optional (~seq #:extra-represented (sub-extra:id ...)) #:defaults ([(sub-extra 1) '()]))
         ;; Touch relation specialized for clos
         (~optional (~seq #:touches touches:id))
         ;; Analysis strategies flags (requires the right parameters too)
         (~optional (~and #:compiled compiled?))
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
                   [ap: (format-id #'ap "~a:" #'ap)]
                   [ls? (format-id #'ls "~a?" #'ls)]
                   [lrk? (format-id #'lrk "~a?" #'lrk)]
                   [ifk? (format-id #'ifk "~a?" #'ifk)]
                   [sk!? (format-id #'sk! "~a?" #'sk!)]
                   [mt? (format-id #'mt "~a?" #'mt)]
                   [clos? (format-id #'clos "~a?" #'clos)]
                   [rlos? (format-id #'rlos "~a?" #'rlos)]
                   [ls: (format-id #'ls "~a:" #'ls)]
                   [lrk: (format-id #'lrk "~a:" #'lrk)]
                   [ifk: (format-id #'ifk "~a:" #'ifk)]
                   [sk!: (format-id #'sk! "~a:" #'sk!)]
                   [mt: (format-id #'mt "~a:" #'mt)]
                   [clos: (format-id #'ev "~a:" #'clos)]
                   [rlos: (format-id #'ev "~a:" #'rlos)]
                   [ev #'ev]
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
                   (syntax-parse syn #:literals (ev)
                     [(_ (ev . args)) (syntax/loc syn (ev . args))]
                     [(_ e:expr) (syntax/loc syn (yield-meaning e))]))
             #'(syntax-rules () [(_ e) (yield-meaning e)])))
       (define eval ;; what does ev mean?
         (quasisyntax/loc stx
           (match e
             [(var l _ x)
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([v #:in-delay ev-σ (lookup-env ρ x)])
                    (yield (co ev-σ k v)))
                  ;; Needed for strict/compiled, but for lazy this introduces
                  ;; an unnecessary administrative reduction.
                  #;
                  (do (ev-σ) ()
                    (yield (dr ev-σ k (lookup-env ρ x)))))]
             [(datum l _ d)
              (λ% (ev-σ ρ k δ)
                  #;
                  (when (memv d (debug-check))
                    (printf "Reached ~a~%" d)
                    (flush-output))
                  (do (ev-σ) () (yield (co ev-σ k d))))]
             [(primr l _ which)
              (define p (primop (compile-primop which)))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k p))))]
             [(lam l _ x e*)
              (define c (compile e*))
              (define fv (free e))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k (clos x c ρ fv)))))]
             [(rlm l _ x r e*)
              (define c (compile e*))
              (define fv (free e))
              (λ% (ev-σ ρ k δ) (do (ev-σ) () (yield (co ev-σ k (rlos x r c ρ fv)))))]
             [(lrc l _ xs es b)
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
                    (yield (ev σ*-lrc c ρ* (lrk (marks-of k) x xs* cs cb ρ* a δ) δ))))]
             [(app l _ e es)
              (define c (compile e))
              (define cs (map compile es))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-app a) #:push ev-σ l δ k])
                    (yield (ev σ*-app c ρ (ls (marks-of k) l 0 cs '() ρ a δ) δ))))]
             [(ife l _ e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-ife a) #:push ev-σ l δ k])
                    (yield (ev σ*-ife c0 ρ (ifk (marks-of k) c1 c2 ρ a δ) δ))))]
             [(st! l _ x e*)
              (define c (compile e*))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-st! a) #:push ev-σ l δ k])
                    (yield (ev σ*-st! c ρ (sk! (marks-of k) (lookup-env ρ x) a) δ))))]
             ;; let/cc is easier to add than call/cc since we make yield
             ;; always make co states for primitives.
             [(lcc l _ x e*)
              (define c (compile e*))
              (λ% (ev-σ ρ k δ)
                  (define x-addr (make-var-contour x δ))
                  (define/ρ ρ* (extend ρ x x-addr))
                  (do (ev-σ) ([σ*-lcc #:join ev-σ x-addr (singleton k)])
                    (yield (ev σ*-lcc c ρ* k δ))))]
             ;; Forms for stack inspection
             #,@(if (given CM?)
                    #`([(grt l _ R e*)
                        (define c (compile e*))
                        (λ% (ev-σ ρ k δ)
                            (do (ev-σ) () (yield (ev ev-σ c ρ (grant k R) δ))))]
                       [(fal l _)
                        (λ% (ev-σ ρ k δ)
                            (do (ev-σ) () (yield (co ev-σ (mt mt-marks) fail))))]
                       [(frm l _ R e)
                        (define c (compile e))
                        (λ% (ev-σ ρ k δ)
                            (do (ev-σ) () (yield (ev ev-σ c ρ (frame k R) δ))))]
                       [(tst l _ R t e*)
                        (define c0 (compile t))
                        (define c1 (compile e*))
                        (λ% (ev-σ ρ k δ)
                            (do (ev-σ) ()
                              (if (OK^ R k ev-σ)
                                  (yield (ev ev-σ c0 ρ k δ))
                                  (yield (ev ev-σ c1 ρ k δ)))))])
                    #'())
             [_ (error 'eval "Bad expr ~a" e)])))

       (define compile-def
         (cond [(given compiled?)
                (define hidden-σ (and (given σ-∆s?) (not (given global-σ?)) (generate-temporary #'hidden-σ)))
                (define hidden-actions (and (given sparse?) (generate-temporary #'hidden-actions)))
                (with-syntax ([(top ...) (listy hidden-σ)]
                              [(topa ...) (listy hidden-actions)]
                              [topp (or hidden-σ #'gσ)])
                  (quasisyntax/loc stx
                    ((define-syntax-rule (... (λ% (gσ ρ k δ) body ...))
                       (λ (top ... topa ... σ-gop ... ρ-op ... k δ-op ...)
                          (syntax-parameterize ([yield (... (... #,yield-ev))]
                                                [top-σ (make-rename-transformer #'topp)]
                                                [target-σ (make-rename-transformer #'gσ)]
                                                [target-actions (make-rename-transformer #'topa)] ...
                                                [top-σ? #t]
                                                [top-actions? #t])
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
           (mk-op-struct state (rσ extra ...) (σ-op ... sub-extra ...)
                         #:fields-as-parameters (sub-extra ...))
           (mk-op-struct co state (k v) expander-flags ...)
           ;; Variable dereference causes problems with strict/compiled
           ;; instantiations because store changes are delayed a step.
           ;; We fix this by making variable dereference a new kind of state.
           (mk-op-struct dr state (k a) expander-flags ...)
           (mk-op-struct ans state (cm v) (cm-op ... v) expander-flags ...
                         #:expander-id ans:)
           (mk-op-struct ap state (l fn-addr v-addrs k δ)
                         (l fn-addr v-addrs k δ-op ...)
                         expander-flags ...)
           ;; Continuation frames
           (mk-op-struct mt (cm) (cm-op ...))
           (mk-op-struct sk! (cm x k) (cm-op ... x k))
           (mk-op-struct ifk (cm t e ρ k δ) (cm-op ... t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (cm x xs es e ρ k δ) (cm-op ... x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (cm l n es vs ρ k δ) (cm-op ... l n es vs ρ-op ... k δ-op ...))
           ;; Values
           (struct primop (which) #:prefab)
           (mk-op-struct clos (x e ρ free) (x e ρ-op ... free) #:expander-id clos:)
           (mk-op-struct rlos (x r e ρ free) (x r e ρ-op ... free) #:expander-id rlos:)
           (define (kont? v) (or (ls? v) (lrk? v) (ifk? v) (sk!? v) (mt? v)))
           ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
           ;; Handling of continuation marks
           (define (marks-of k)
             #,(if (given CM?)
                   #'(match k
                       [(or (mt: cm)
                            (sk!: cm _ _)
                            (ifk: cm _ _ _ _ _)
                            (lrk: cm _ _ _ _ _ _ _)
                            (ls: cm _ _ _ _ _ _ _)) cm])
                   #'#f))
           (define (tail-of k)
             #,(if (given CM?)
                   #'(match k
                       [(mt: cm) #f]
                       [(sk!: cm l k) k]
                       [(ifk: cm t e ρ k δ) k]
                       [(lrk: cm x xs es e ρ k δ) k]
                       [(ls: cm l n es vs ρ k δ) k])
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
                        (ls (set-mark cm R) l n es vs ρ k δ)])
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
                        (ls (frame-mark cm R) l n es vs ρ k δ)])
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
                  #`((mk-touches touches clos: rlos: list #,(zero? (attribute K))))
                  #'())
           (splicing-syntax-parameterize ([target-σ? (and #,σ-threading? 'threading)]
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
                          #'(e #,@(listy (and (given σ-∆s?) (not (given global-σ?)) #'top-σ))
                               #,@(listy (and (given sparse?) #'target-actions))
                               σ-gop ... ρ-op ... k δ-op ...)]))
                     (define-match-expander ev: ;; inert, but introduces bindings
                       (syntax-rules () [(_ . args) (list . args)]))))
                  (quasisyntax/loc stx
                    ((mk-op-struct ev state (e ρ k δ) (e ρ-op ... k δ-op ...)
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
              (do (σ₀) () (yield (ev σ₀ (compile e) (hash) (mt mt-marks) '())))))

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
           (define-syntax mk-prims (mk-mk-prims #,(given global-σ?) #,σ-passing?*
                                                #,(given σ-∆s?) #,(given compiled?)
                                                #,(given sparse?)
                                                #,(attribute K)))
           (mk-prims prim-meaning compile-primop co clos? rlos?)
           ;; [Rel State State]
           (define (step state)
             (match state
               ;; Only for compiled/strict
               #;
               [(dr: dr-σ k a)
                (generator
                 (do (dr-σ) ([v #:in-delay dr-σ a]) (yield (co dr-σ k v))))]
               [(co: co-σ extra ... k v)
                (match k
                  [(mt: cm) (generator (do (co-σ) ([v #:in-force co-σ v])
                                     (yield (ans co-σ cm v))))]

                  ;; We need this intermediate step so that σ-∆s work.
                  ;; The above join is not merged into the store until
                  ;; after the step, and the address is needed by the call.
                  [(ls: cm l n '() v-addrs ρ a δ)
                   (define v-addr (make-var-contour (cons l n) δ))
                   (define args (reverse (cons v-addr v-addrs)))
                   (generator
                    (do (co-σ) ([σ*-ls #:join-forcing co-σ v-addr v]
                                [k #:in-get σ*-ls a])
                      (yield (ap σ*-ls l (first args) (rest args) k δ))))]

                  [(ls: cm l n (list-rest e es) v-addrs ρ a δ)
                   (define v-addr (make-var-contour (cons l n) δ))
                   (generator
                    (do (co-σ) ([σ*-lsn #:join-forcing co-σ v-addr v])
                      (yield (ev σ*-lsn e ρ
                                 (ls cm l (add1 n) es (cons v-addr v-addrs) ρ a δ) δ))))]
                  [(ifk: cm t e ρ a δ)
                   (generator
                    (do (co-σ) ([k* #:in-get co-σ a]
                                [v #:in-force co-σ v])
                      (yield (ev co-σ (if v t e) ρ k* δ))))]
                  [(lrk: cm x '() '() e ρ a δ)
                   (generator
                    (do (co-σ) ([σ*-lrk #:join-forcing co-σ (lookup-env ρ x) v]
                                [k* #:in-get σ*-lrk a])
                      (yield (ev σ*-lrk e ρ k* δ))))]
                  [(lrk: cm x (cons y xs) (cons e es) b ρ a δ)
                   (generator
                    (do (co-σ) ([σ*-lrkn #:join-forcing co-σ (lookup-env ρ x) v])
                      (yield (ev σ*-lrkn e ρ (lrk cm y xs es b ρ a δ) δ))))]
                  [(sk!: cm l a)
                   (generator
                    (do (co-σ) ([σ*-sk! #:join-forcing co-σ l v]
                                [k* #:in-get σ*-sk! a])
                      (yield (co σ*-sk! k* (void)))))]
                  [_ (error 'step "Bad continuation ~a" k)])]

               ;; v is not a value here. It is an address.
               [(ap: ap-σ extra ... l fn-addr arg-addrs k δ)
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
                             (log-info "Arity error on ~a at ~a" f l)
                             (yield (ap ap-σ l fn-addr arg-addrs k δ))])]
                     [(rlos: xs r e ρ _)
                      (cond [(<= (length xs) (length arg-addrs))
                             (do (ap-σ)
                                 ([(ρ* σ*-clos δ*) #:bind-rest ρ ap-σ l δ xs r arg-addrs])
                               (yield (ev σ*-clos e ρ* k δ*)))]
                            ;; Yield the same state to signal "stuckness".
                            [else
                             (log-info "Arity error on ~a at ~a" f l)
                             (yield (ap ap-σ l fn-addr arg-addrs k δ))])]
                     [(primop o) (prim-meaning o ap-σ l δ k arg-addrs)]
                     [(? kont? k)
                      ;; continuations only get one argument.
                      (cond [(and (pair? arg-addrs) (null? (cdr arg-addrs)))
                             (do (ap-σ) ([v #:in-delay ap-σ (car arg-addrs)])
                               (yield (co ap-σ k v)))]
                            [else
                             (log-info "Called continuation with wrong number of arguments (~a): ~a at ~a"
                                       (length arg-addrs) k l)
                             (yield (ap ap-σ l fn-addr arg-addrs k δ))])]
                     [(== ●) (=> fail)
                      (log-debug "implement ●-call")
                      (fail)]
                     [_
                      (log-info "Called non-function ~a" f)
                      (yield (ap ap-σ l fn-addr arg-addrs k δ))])))]

               ;; this code is dead when running compiled code.
               [(ev: ev-σ extra ... e ρ k δ)
                #,(if (given compiled?)
                      #'(generator (do (ev-σ) () (yield (ev ev-σ e ρ k δ))))
                      eval)]

               [(ans: ans-σ cm v) (generator (do (ans-σ) () (yield (ans ans-σ cm v))))]
               [_ (error 'step "Bad state ~a" state)]))

#;
           (trace step)

           )))))]))
