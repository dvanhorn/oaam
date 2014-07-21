#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt" "primitives.rkt" "parse.rkt"
         "notation.rkt" "op-struct.rkt" "do.rkt" "add-lib.rkt"
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax racket/base
                     syntax/parse/experimental/template)
         racket/fixnum
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
                   [clos? (format-id #'clos "~a?" #'clos)]
                   [rlos? (format-id #'rlos "~a?" #'rlos)]
                   [primop: (format-id #'primop "~a:" #'primop)]
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

       (define (continue-step co-σ v cm φ k**)
         (with-syntax ([(co-σ v cm φ k**) (list co-σ v cm φ k**)])
           (if (given compiled?)
               (quasisyntax/loc stx
                 (φ #,@(listy (and (given σ-∆s?) (not (given global-σ?)) #'top-σ))
                    #,@(listy (and (not (given global-σ?)) #'co-σ))
                    v
                    cm-op ... k**))
               (quasisyntax/loc stx
                 (match φ
                   #,step-ls
                   #,step-ifk
                   #,step-lrk
                   #,step-sk!)))))

       (define eval ;; what does ev mean?
         (syntax/loc stx
           (match e
             [(var l x)
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([v #:in-delay ev-σ (lookup-env ρ x)])
                    (yield (co ev-σ k v)))
                  ;; Needed for strict/compiled, but for lazy this introduces
                  ;; an unnecessary administrative reduction.
                  #;
                  (do (ev-σ) ()
                    (yield (dr ev-σ k (lookup-env ρ x)))))]
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
                    (yield (ev σ*-lrc c ρ* (kcons (marks-of k) (lrk x xs* cs cb ρ* δ) a) δ))))]
             [(app l e es)
              (define c (compile e))
              (define cs (map compile es))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-app a) #:push ev-σ l δ k])
                    (yield (ev σ*-app c ρ (kcons (marks-of k) (ls l 0 cs '() ρ δ) a) δ))))]
             [(ife l e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-ife a) #:push ev-σ l δ k])
                    (yield (ev σ*-ife c0 ρ (kcons (marks-of k) (ifk c1 c2 ρ δ) a) δ))))]
             [(st! l x e)
              (define c (compile e))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ([(σ*-st! a) #:push ev-σ l δ k])
                    (yield (ev σ*-st! c ρ (kcons (marks-of k) (sk! (lookup-env ρ x)) a) δ))))]
             ;; let/cc is easier to add than call/cc since we make yield
             ;; always make co states for primitives.
             [(lcc l x e)
              (define c (compile e))
              (λ% (ev-σ ρ k δ)
                  (define x-addr (make-var-contour x δ))
                  (define/ρ ρ* (extend ρ x x-addr))
                  (do (ev-σ) ([σ*-lcc #:join ev-σ x-addr (singleton k)])
                    (yield (ev σ*-lcc c ρ* k δ))))]
             ;; Forms for stack inspection
             [(grt l R e)
              (define c (compile e))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) () (yield (ev ev-σ c ρ (grant k R) δ))))]
             [(fal l)
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) () (yield (co ev-σ (mt mt-marks) fail))))]
             [(frm l R e)
              (define c (compile e))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) () (yield (ev ev-σ c ρ (frame k R) δ))))]
             [(tst l R t e)
              (define c0 (compile t))
              (define c1 (compile e))
              (λ% (ev-σ ρ k δ)
                  (do (ev-σ) ()
                    (if (OK^ R k ev-σ)
                        (yield (ev ev-σ c0 ρ k δ))
                        (yield (ev ev-σ c1 ρ k δ)))))]
             [_ (error 'eval "Bad expr ~a" e)])))

       (define compile-def
         (cond [(given compiled?)
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
                     (define-syntax-rule (... (λφ (gσ v cm k) body ...))
                       (λ (top ... σ-gop ... v cm-op ... k)
                          (generator
                           (syntax-parameterize ([top-σ (make-rename-transformer #'topp)]
                                                 [target-σ (make-rename-transformer #'gσ)]
                                                 [top-σ? #t])
                             body (... ...)))))
                     #,(if (given collect-hash)
                           (quasisyntax/loc stx
                             (define (compile e)
                               (define form #,eval)
                               (hash-set! collect-hash form e)
                               form))
                           (quasisyntax/loc stx (define (compile e) #,eval))))))]
               [else
                ;; brittle, since other identifiers must be the same in ev:
                (syntax/loc stx
                  ((... (define-syntax-rule (λ% (ev-σ ρ k δ) body ...)
                          (generator body ...)))
                   (... (define-syntax-rule (λφ (gσ v cm k) body ...)
                          (let () body ...)))
                   (define compile values)))]))

       (define (mk-k-struct id apparent represented to-step)
         (with-syntax ([id: (format-id id "~a:" id)]
                       [id-rep (format-id id "~a-container" id)]
                       [mk-id (format-id id "mk-~a" id)]
                       [(id-sels ...) (map (λ (f)
                                          (format-id id "~a-container-~a" id (syntax-e f)))
                                       (syntax->list represented))])
           (if (given compiled?)
               (values #f
                       #`(begin
                           (define-values (mk-id id-sels ...)
                             (let ()
                               (struct id-rep (fn . #,represented)
                                       #:property prop:procedure 0
                                       ;; Need to throw away the closure from equality concerns,
                                       ;; since structural comparison is still needed.
                                       #:methods gen:equal+hash
                                       [(define (equal-proc x y rec)
                                          (and (rec (id-sels x) (id-sels y)) ...))
                                        (define (hash-proc x rec)
                                          (lassoc fxxor (rec (id-sels x)) ...))
                                        (define (hash2-proc x rec)
                                          (lassoc fxxor (rec (id-sels x)) ...))]
                                       #:transparent)
                               ;; XXX: duplicates storage in closure and struct, but
                               ;; that's the price we pay for inspection.
                               (values (λ #,represented
                                          (id-rep #,to-step . #,represented))
                                       id-sels ...)))
                           (define-syntax-rule (#,id . #,apparent) (mk-id . #,represented))))
               (values #`[(id: . #,apparent) #,to-step]
                       #`(mk-op-struct #,id #,apparent #,represented)))))

       (define-values (step-ifk ifk-rep)
         (mk-k-struct #'ifk #'(t e ρ δ) #'(t e ρ-op ... δ-op ...)
                      #'(λφ (co-σ v cm k*)
                          (do (co-σ) ([k** #:in-delay-kont co-σ k*]
                                      [v #:in-force co-σ v])
                            (yield (ev co-σ (if v t e) ρ k** δ))))))

       (define-values (step-sk! sk!-rep)
         (mk-k-struct #'sk! #'(l) #'(l)
                      #'(λφ (co-σ v cm k*)
                            (do (co-σ) ([σ*-sk! #:join-forcing co-σ l v]
                                        [k** #:in-delay-kont σ*-sk! k*])
                              (yield (co σ*-sk! k** (void)))))))

       (define-values (step-lrk lrk-rep)
         (mk-k-struct #'lrk #'(x xs es b ρ δ) #'(x xs es b ρ-op ... δ-op ...)
                      #'(match* (xs es)
                        [('() '())
                         (λφ (co-σ v cm k*)
                             (do (co-σ) ([σ*-lrk #:join-forcing co-σ (lookup-env ρ x) v]
                                         [k** #:in-delay-kont σ*-lrk k*])
                               (yield (ev σ*-lrk b ρ k** δ))))]
                        [((cons y xs) (cons e es))
                         (λφ (co-σ v cm k*)
                             (do (co-σ) ([σ*-lrkn #:join-forcing co-σ (lookup-env ρ x) v])
                               (yield (ev σ*-lrkn e ρ (kcons cm (lrk y xs es b ρ δ) k*) δ))))])))

       (define-values (step-ls ls-rep)
         (mk-k-struct #'ls #'(l n es vs ρ δ) #'(l n es vs ρ-op ... δ-op ...)
                      #'(match es
                        ['()
                         ;; We need this intermediate step so that σ-∆s work.
                         ;; The above join is not merged into the store until
                         ;; after the step, and the address is needed by the call.
                         (λφ (co-σ v cm k*)
                             (define v-addr (make-var-contour (cons l n) δ))
                             (define args (reverse (cons v-addr vs)))
                             (do (co-σ) ([σ*-ls #:join-forcing co-σ v-addr v]
                                         [k #:in-delay-kont σ*-ls k*])
                               (yield (ap σ*-ls l (first args) (rest args) k δ))))]
                        [(cons e es)
                         (λφ (co-σ v cm k*)
                             (define v-addr (make-var-contour (cons l n) δ))
                             (do (co-σ) ([σ*-lsn #:join-forcing co-σ v-addr v])
                               (yield (ev σ*-lsn e ρ
                                          (kcons cm (ls l (add1 n) es (cons v-addr vs) ρ δ) k*) δ))))])))

       (quasitemplate/loc stx
         (begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct co (rσ k v) (σ-op ... k v) expander-flags ...)
           ;; Pushdown analysis has calling contexts
           (mk-op-struct ctx (σ-token l fn-addr v-addrs δ) (σ-token l fn-addr v-addrs δ-op ...))
           (mk-op-struct relevant (rσ v) (σ-op ... v))
           ;; Variable dereference causes problems with strict/compiled
           ;; instantiations because store changes are delayed a step.
           ;; We fix this by making variable dereference a new kind of state.
           (mk-op-struct dr (rσ k a) (σ-op ... k a) expander-flags ...)
           (mk-op-struct ans (rσ cm v) (σ-op ... cm-op ... v) expander-flags ...
                         #:expander-id ans:)
           (mk-op-struct ap (rσ l fn-addr v-addrs k δ)
                         (σ-op ... l fn-addr v-addrs k δ-op ...)
                         expander-flags ...)
           ;; Continuations
           (mk-op-struct mt (cm) (cm-op ...))
           (mk-op-struct kcons (cm φ κ) (cm-op ... φ κ))
           ;; also addr, for lazy-nondet.
           ;; Continuation frames come after do definition
           ;; Values
           (struct primop (which) #:prefab)
           (mk-op-struct clos (x e ρ free) (x e ρ-op ... free) #:expander-id clos:)
           (mk-op-struct rlos (x r e ρ free) (x r e ρ-op ... free) #:expander-id rlos:)
           (define (kont? v) (or (mt? v) (kcons? v) (addr? v) (ctx? v)))
           ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
           ;; Handling of continuation marks
           (define (marks-of k)
             #,(if (given CM?)
                   #'(match k
                       [(or (mt: cm)
                            (kcons: cm _ _)) cm]
                       [(? addr?) (error 'marks-of "todo: addr")])
                   #'#f))
           (define (tail-of k)
             #,(if (given CM?)
                   #'(match k
                       [(mt: _) #f]
                       [(kcons: _ _ k) k]
                       [(? addr?) (error 'tail-of "todo: addr")])
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
                       [(kcons: cm φ k)
                        (kcons (set-mark cm R) φ k)]
                       [(? addr?) (error 'grant "todo: addr")])
                   #'#f))
           (define (frame k R)
             #,(if (given CM?)
                   #'(match k
                       [(mt: cm)
                        (mt (frame-mark cm R))]
                       [(kcons: cm φ k)
                        (kcons (frame-mark cm R) φ k)]
                       [(? addr?) (error 'frame "todo: addr")])
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
           #,ifk-rep
           #,sk!-rep
           #,lrk-rep
           #,ls-rep

           ;; ev is special since it can mean "apply the compiled version" or
           ;; make an actual ev state to later interpret.
           #,@(if (given compiled?)
                  (quasisyntax/loc stx
                    ((define-syntax (ev syn)
                       (syntax-case syn ()
                         ;; gσ only optional if it's global
                         [(_ gσ e ρ k δ)
                          #'(e #,@(listy (and (given σ-∆s?) (not (given global-σ?)) #'top-σ))
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
               [(co: co-σ k v)
                (generator
                    ;; Pushdown analysis that memoizes needs the rest of the state
                    ;; to say that the context in k evaluates to that rest of state.
                  (do (co-σ) ([#:in-pop-kont ctx? (relevant co-σ v) k
                               #:mts [(mt: cm)
                                      (do (co-σ) ([v #:in-force co-σ v])
                                        (yield (ans co-σ cm v)))]
                               #:frames [(kcons: cm φ k*)
                                         #,(continue-step #'co-σ #'v #'cm #'φ #'k*)]])
                    (void)))]

               ;; v is not a value here. It is an address.
               [(ap: ap-σ l fn-addr arg-addrs k δ)
                (generator
                 (do (ap-σ) ([k* #:bind-calling-context (ctx (get-σ-token ap-σ)
                                                             l fn-addr arg-addrs δ) k
                                 #:short-circuit
                                 [(relevant: co-σ v)
                                  (do (co-σ) () (yield (co co-σ k v)))]]
                             [f #:in-get ap-σ fn-addr])
                   (match f
                     [(clos: xs e ρ _)
                      (cond [(= (length xs) (length arg-addrs))
                             (do (ap-σ)
                                 ([(ρ* σ*-clos δ*) #:bind ρ ap-σ l δ xs arg-addrs])
                               (yield (ev σ*-clos e ρ* k* δ*)))]
                            ;; Yield the same state to signal "stuckness".
                            [else
                             (log-info "Arity error on ~a at ~a" f l)
                             (yield (ap ap-σ l fn-addr arg-addrs k* δ))])]
                     [(rlos: xs r e ρ _)
                      (cond [(<= (length xs) (length arg-addrs))
                             (do (ap-σ)
                                 ([(ρ* σ*-clos δ*) #:bind-rest ρ ap-σ l δ xs r arg-addrs])
                               (yield (ev σ*-clos e ρ* k* δ*)))]
                            ;; Yield the same state to signal "stuckness".
                            [else
                             (log-info "Arity error on ~a at ~a" f l)
                             (yield (ap ap-σ l fn-addr arg-addrs k* δ))])]
                     [(primop o) (prim-meaning o ap-σ l δ k* arg-addrs)]
                     [(? kont? kv) ;; TODO: add χ and approximation for call/cc and pushdown
                      ;; continuations only get one argument.
                      (cond [(and (pair? arg-addrs) (null? (cdr arg-addrs)))
                             (do (ap-σ) ([v #:in-delay ap-σ (car arg-addrs)])
                               (yield (co ap-σ kv v)))]
                            [else
                             (log-info "Called continuation with wrong number of arguments (~a): ~a at ~a"
                                       (length arg-addrs) kv l)
                             (yield (ap ap-σ l fn-addr arg-addrs kv δ))])]
                     [(== ●) (=> fail)
                      (log-debug "implement ●-call")
                      (fail)]
                     [_
                      (log-info "Called non-function ~a" f)
                      (yield (ap ap-σ l fn-addr arg-addrs k* δ))])))]

               ;; this code is dead when running compiled code.
               [(ev: ev-σ e ρ k δ)
                #,(if (given compiled?)
                      #'(generator (do (ev-σ) () (yield (ev ev-σ e ρ k δ))))
                      eval)]

               [(ans: ans-σ cm v) (generator (do (ans-σ) () (yield (ans ans-σ cm v))))]
               [_ (error 'step "Bad state ~a" state)]))

#;
           (trace step)

           )))))]))

(define-syntax lassoc
  (syntax-rules ()
    [(_ fn) (error 'lassoc "Need at least one arg")]
    [(_ fn a) a]
    [(_ fn a b) (fn a b)]
    [(_ fn a b . rest) (fn a (lassoc fn b . rest))]))
