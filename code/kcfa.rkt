#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt" "primitives.rkt" "parse.rkt"
         "parameters.rkt" "egal-box.rkt"
         "notation.rkt" "op-struct.rkt" "do.rkt" "add-lib.rkt"
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax racket/base
                     syntax/parse/experimental/template)
         racket/stxparam racket/splicing
         racket/trace)
(provide mk-analysis debug-check
         (for-syntax analysis-parameters parameters-minus))
(define debug-check (make-parameter '()))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

(define (cont-arity-error given k l)
  (log-info "Called continuation with wrong number of arguments (~a): ~a at ~a"
            given k l))

(define (non-function-error f)
  (log-info "Called non-function ~a" f))

(begin-for-syntax
 (define (colonfy name) (format-id name "~a:" name))
 (define (:? id) (list (colonfy id) (format-id id "~a?" id)))
 (define-splicing-syntax-class analysis-parameters
   #:attributes (state ans dr ar ap co ev call
                 mt sk! ifk lrk ls clos rlos kont?
                 (extra 1)
                 ast touches-id prep-fn
                 ;; others
                 fixpoint aval compiled? pushdown? CM? mark-set
                 global-σ? wide? K generators?
                 (all 1))
   (pattern
    (~and
     (~seq all ...)
     (~seq
      (~or
       (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
       ;; Name representations' structs
       (~optional (~seq #:state state:id) #:defaults ([state (generate-temporary #'state)]))
       (~optional (~seq #:ans ans:id) #:defaults ([ans (generate-temporary #'ans)]))
       (~optional (~seq #:dr dr:id) #:defaults ([dr (generate-temporary #'dr)]))
       (~optional (~seq #:ar ar:id) #:defaults ([ar (generate-temporary #'ar)]))
       (~optional (~seq #:ap ap:id) #:defaults ([ap (generate-temporary #'ap)]))
       (~optional (~seq #:co co:id) #:defaults ([co (generate-temporary #'co)]))
       (~optional (~seq #:ev ev:id) #:defaults ([ev (generate-temporary #'ev)]))
       (~optional (~seq #:call call:id) #:defaults ([call (generate-temporary #'call)]))
       ;; Continuation frames
       (~optional (~seq #:mt mt:id) #:defaults ([mt (generate-temporary #'mt)]))
       (~optional (~seq #:sk! sk!:id) #:defaults ([sk! (generate-temporary #'sk!)]))
       (~optional (~seq #:ifk ifk:id) #:defaults ([ifk (generate-temporary #'ifk)]))
       (~optional (~seq #:lrk lrk:id) #:defaults ([lrk (generate-temporary #'lrk)]))
       (~optional (~seq #:ls ls:id) #:defaults ([ls (generate-temporary #'ls)]))
       (~optional (~seq #:clos clos:id) #:defaults ([clos (generate-temporary #'clos)]))
       (~optional (~seq #:rlos rlos:id) #:defaults ([rlos (generate-temporary #'rlos)]))
       (~optional (~seq #:kont? kont?:id) #:defaults ([kont? (generate-temporary #'kont?)]))
       ;; Integrated analysis information stored in each state
       (~optional (~seq #:extra (extra:id ...)) #:defaults ([(extra 1) '()]))
       (~optional (~seq #:ast ast:id) #:defaults ([ast (generate-temporary #'ast)]))
       ;; Touch relation specialized for clos
       (~optional (~seq #:touches touches-id:id) #:defaults ([touches-id (generate-temporary #'touches-id)]))
       (~optional (~seq #:fixpoint fixpoint:expr) #:defaults ([fixpoint #'fix]))
       (~optional (~seq #:prepare prep-fn:expr))
       ;; Analysis strategies flags (requires the right parameters too)
       (~optional (~and #:compiled compiled?))
       (~optional (~and #:pushdown pushdown?))
       ;; Continuation marks incur a representation overhead.
       ;; We allow this feature to be disabled for benchmarking analysis of
       ;; languages that do not have continuation marks.
       (~optional (~seq (~and #:CM CM?) mark-set)
                  #:defaults ([mark-set #'∅]))
       (~optional (~and #:global-σ global-σ?))
       (~optional (~and #:wide wide?))
       (~optional (~or (~and (~seq #:kcfa k-nat-or-∞)
                             (~bind [K (syntax-e #'k-nat-or-∞)]))
                       (~and #:1cfa (~bind [K 1])))
                  #:defaults ([K 0]))
       (~optional (~and #:generators generators?))) ;; any preprocessing?
      ...))))

 (define (parameters-minus o kws)
   (define (ok? kw stx) 
     (if (and stx (not (memq kw kws)))
         (list kw stx)
         '()))
   (define (add? kw v)
     (listy (and v (not (memq kw kws)) kw)))
   (syntax-parse o
     [(p:analysis-parameters)
      (append
       (ok? '#:state #'p.state)
       (ok? '#:ans #'p.ans)
       (ok? '#:dr #'p.dr)
       (ok? '#:ar #'p.ar)
       (ok? '#:ap #'p.ap)
       (ok? '#:co #'p.co)
       (ok? '#:ev #'p.ev)
       (ok? '#:mt #'p.mt)
       (ok? '#:sk! #'p.sk!)
       (ok? '#:ifk #'p.ifk)
       (ok? '#:lrk #'p.lrk)
       (ok? '#:ls #'p.ls)
       (ok? '#:clos #'p.clos)
       (ok? '#:rlos #'p.rlos)
       (ok? '#:kont? #'p.kont?)
       (ok? '#:extra #'(p.extra ...))
       (ok? '#:aval #'p.aval)
       (ok? '#:fixpoint #'p.fixpoint)
       (ok? '#:touches #'p.touches-id)
       (ok? '#:ast #'p.ast)
       (ok? '#:prepare (attribute p.prep-fn))
       (ok? '#:kcfa (attribute p.K))
       (if (and (attribute p.CM?)
                (not (memq '#:CM kws)))
           (list '#:CM #'p.mark-set)
           '())
       (add? '#:wide (attribute p.wide?))
       (add? '#:compile (attribute p.compiled?))
       (add? '#:global-σ (attribute p.global-σ?))
       (add? '#:generators (attribute p.generators?))
       (add? '#:pushdown (attribute p.pushdown?)))])))

(define-syntax (mk-analysis stx)
  (syntax-parse stx
    [(_ pa:analysis-parameters)
     #:do [(define-syntax-rule (given kw) (syntax? (attribute kw)))
           (define-syntax-rule (implies ante concl) (if ante concl #t))]
     #:fail-unless (implies (given pa.global-σ?) (given pa.wide?))
     "Cannot globalize narrow stores."
     (define-values (wide? global-σ? generators? K CM? compiled? pushdown?)
       (values (given pa.wide?) (given pa.global-σ?) (given pa.generators?) (attribute pa.K)
               (given pa.CM?) (given pa.compiled?) (given pa.pushdown?)))
     (with-syntax*
         ([((ρ-op ...) (δ-op ...) (l-op ...))
           (if (zero? K) #'(() () ()) #'((ρ) (δ) (l)))]
          ;; drop the pa. from all the representation names
          [(state ans dr ar ap co ev call
            mt sk! ifk lrk ls clos rlos kont?
            (extra ...) (extra-ids ...)
            aval fixpoint ast touches-id prep-fn mark-set)
           (list #'pa.state #'pa.ans #'pa.dr #'pa.ar #'pa.ap #'pa.co #'pa.ev #'pa.call
                 #'pa.mt #'pa.sk! #'pa.ifk #'pa.lrk #'pa.ls #'pa.clos #'pa.rlos #'pa.kont?
                 #'(pa.extra ...) (generate-temporaries #'(pa.extra ...))
                 #'pa.aval #'pa.fixpoint #'pa.ast #'pa.touches-id #'pa.prep-fn #'pa.mark-set)]
          [(ev: co: ap: call:) (map colonfy (list #'ev #'co #'ap #'call))]
          [ast-fv (format-id #'ast "~a-fv" #'ast)]
          [((ls: ls?)
            (lrk: lrk?)
            (ifk: ifk?)
            (sk!: sk!?)
            (mt: mt?)
            (clos: clos?)
            (rlos: rlos?))
           (map :? (syntax->list #'(ls lrk ifk sk! mt clos rlos)))]
          [(cm-op ...) (listy (and CM? #'cm))]
          ;; represent rσ explicitly in all states?
          [(σ-op ...) (if wide? #'() #'(rσ))]
          ;; If rσ not part of state and not global, it is passed
          ;; in as (cons rσ state), so expand accordingly.
          [(expander-flags ...)
           (cond [(and wide? (not global-σ?))
                  #'(#:expander #:without-first)]
                 [else #'()])])
       (define yield-ev
         #`(let ([yield-tr (syntax-parameter-value #'yield)])
             #,(if compiled?
                   #'(λ (syn)
                        (syntax-parse syn #:literals (ev)
                          [(_ (ev . args)) (syntax/loc syn (ev . args))]
                          [(_ e:expr) (yield-tr #'(yield e))]))
                   #'yield-tr)))

       (define eval ;; what does ev mean?
         (quasisyntax/loc stx
           (match e
             [(var l _ x)
              (λ% (σ ρ k δ)
                  (do (σ) ([v #:in-delay σ (lookup-env ρ x)])
                    (yield (co σ k v)))
                  ;; Needed for strict/compiled, but for lazy this introduces
                  ;; an unnecessary administrative reduction.
                  #;
                  (do (σ) ()
                    (yield (dr σ k (lookup-env ρ x)))))]
             [(datum l _ d)
              (λ% (σ ρ k δ)
                  (when (memv d (debug-check))
                    (printf "Reached ~a~%" d)
                    (flush-output))
                  (do (σ) () (yield (co σ k d))))]
             [(primr l _ which fallback)
              (define p (primop (compile-primop which)
                                fallback
                                (hash-ref prim-arities which)))
              (λ% (σ ρ k δ) (do (σ) () (yield (co σ k p))))]
             [(pfl l _ fallback e)
              (define c (compile e))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-pfl a) #:push σ l δ k])
                    (yield (ev σ*-pfl c (restrict-to-set ρ fv) (pfk (marks-of k) fallback a) δ))))]
             [(lam l _ x e*)
              (define c (compile e*))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ) (do (σ) () (yield (co σ k (clos x c (restrict-to-set ρ fv))))))]
             [(rlm l _ x r e*)
              (define c (compile e*))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ) (do (σ) () (yield (co σ k (rlos x r c (restrict-to-set ρ fv))))))]
             [(lrc l _ (and xs (cons x xs*)) (cons e es) b)
              (define c (compile e))
              (define cs (map compile es))
              (define cb (compile b))
              (define ss (map (λ _ nothing) xs))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ)
                  (define as (map (λ (x) (make-var-contour l x δ)) xs))
                  (define/ρ ρ* (extend* ρ xs as))
                  (define/ρ ρe (restrict-to-set ρ* fv))
                  (do (σ) ([(σ0 a) #:push σ l δ k]
                           [σ*-lrc #:join* σ0 as ss])
                    (yield (ev σ*-lrc c ρe (lrk (marks-of k) x xs* cs cb ρ* a δ) δ))))]
             [(lte l _ (cons x xs) (cons e es) b)
              (define c (compile e))
              (define cs (map compile es))
              (define cb (compile b))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-app a) #:push σ l δ k])
                    (yield (ev σ*-app c (restrict-to-set ρ fv)
                               (ltk (marks-of k) l x xs cs '() '() cb ρ a δ)
                               δ))))]
             [(app l _ e es)
              (define c (compile e))
              (define cs (map compile es))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-app a) #:push σ l δ k])
                    (yield (ev σ*-app c (restrict-to-set ρ fv)
                               (ls (marks-of k) l 0 cs '() ρ a δ)
                               δ))))]
             [(ife l _ e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (define fv (ast-fv c0))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-ife a) #:push σ l δ k])
                    (yield (ev σ*-ife c0 (restrict-to-set ρ fv)
                               (ifk (marks-of k) c1 c2 ρ a δ) δ))))]
             [(st! l _ x e*)
              (define c (compile e*))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ)
                  (do (σ) ([(σ*-st! a) #:push σ l δ k])
                    (yield (ev σ*-st! c (restrict-to-set ρ fv) (sk! (marks-of k) (lookup-env ρ x) a) δ))))]
             ;; let/cc is easier to add than call/cc since we make yield
             ;; always make co states for primitives.
             [(lcc l _ x e*)
              (define c (compile e*))
              (define fv (ast-fv c))
              (λ% (σ ρ k δ)
                  (define x-addr (make-var-contour l x δ))
                  (define/ρ ρ* (restrict-to-set (extend ρ x x-addr) fv))
                  (do (σ) ([σ*-lcc #:join σ x-addr (singleton k)])
                    (yield (ev σ*-lcc c ρ* k δ))))]
             ;; Forms for stack inspection
             #,@(if CM?
                    #`([(grt l _ R e*)
                        (define c (compile e*))
                        (λ% (σ ρ k δ)
                            (do (σ) () (yield (ev σ c ρ (grant k R) δ))))]
                       [(fal l _)
                        (λ% (σ ρ k δ)
                            (do (σ) () (yield (co σ (mt mt-marks) fail))))]
                       [(frm l _ R e)
                        (define c (compile e))
                        (λ% (σ ρ k δ)
                            (do (σ) () (yield (ev σ c ρ (frame k R) δ))))]
                       [(tst l _ R t e*)
                        (define c0 (compile t))
                        (define c1 (compile e*))
                        (λ% (σ ρ k δ)
                            (do (σ) ()
                              (if (OK^ R k σ)
                                  (yield (ev σ c0 ρ k δ))
                                  (yield (ev σ c1 ρ k δ)))))])
                    #'())
             [_ (error 'eval "Bad expr ~a" e)])))

       (define compile-def
         (cond [compiled?
                (quasisyntax/loc stx
                    ((define-syntax-rule (... (λ% (gσ ρ k δ) body ...))
                       (tλ (#:σ gσ ρ-op ... k δ-op ...) body (... ...)))
                     (define (compile e) (ast #,eval (free e)))))]
               [else
                ;; brittle, since other identifiers must be the same in ev:
                (syntax/loc stx
                  ((... (define-syntax-rule (λ% (σ ρ k δ) body ...)
                          (generator body ...)))
                   (define compile values)))]))

       (quasitemplate/loc stx
         (begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct state (rσ extra ...) (σ-op ... extra ...)
                         #:fields-as-parameters (extra ...))
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
           ;; Need another step for sparse-narrow to get better precision
           (mk-op-struct call state (l fnv v-addrs k δ)
                         (l fnv v-addrs k δ-op ...)
                         expander-flags ...)
           (mk-op-struct lt state (e ρ xs as k δ) (e ρ-op ... xs as k δ-op ...) expander-flags ...)
           ;; Continuation frames
           (mk-op-struct mt (cm) (cm-op ...))
           (mk-op-struct sk! (cm x k) (cm-op ... x k))
           (mk-op-struct ifk (cm t e ρ k δ) (cm-op ... t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (cm x xs es e ρ k δ) (cm-op ... x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (cm l n es vs ρ k δ) (cm-op ... l n es vs ρ-op ... k δ-op ...))
           (mk-op-struct ltk (cm l x xs es x-done v-addrs e ρ k δ)
                         (cm-op ... l x xs es x-done v-addrs e ρ-op ... k δ-op ...))
           (mk-op-struct pfk (cm fallback k) (cm-op ... fallback k))
           ;; Values
           (mk-op-struct clos (x e ρ) (x e ρ-op ...) #:expander-id clos:)
           (mk-op-struct rlos (x r e ρ) (x r e ρ-op ...) #:expander-id rlos:)
           (define (kont? v) (or (ls? v) (lrk? v) (ltk? v) (ifk? v) (sk!? v) (mt? v) (pfk? v)))

           #,(if compiled?
                 #'(struct ast (compiled fv) #:property prop:procedure (struct-field-index compiled))
                 #'(define ast-fv free))

           ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
           ;; handling of continuation marks
           (define (marks-of k)
             #,(if CM?
                   #'(match k
                       [(or (mt: cm)
                            (sk!: cm _ _)
                            (ifk: cm _ _ _ _ _)
                            (lrk: cm _ _ _ _ _ _ _)
                            (ltk: cm _ _ _ _ _ _ _ _ _ _)
                            (ls: cm _ _ _ _ _ _ _)
                            (pfk: cm _ _)) cm])
                   #'#f))
           (define (tail-of k)
             #,(if CM?
                   #'(match k
                       [(mt: cm) #f]
                       [(sk!: cm l k) k]
                       [(ifk: cm t e ρ k δ) k]
                       [(lrk: cm x xs es e ρ k δ) k]
                       [(ltk: cm l x xs es xd va e ρ k δ) k]
                       [(ls: cm l n es vs ρ k δ) k]
                       [(pfk: cm f k) k])
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
             #,(if CM?
                   #'(match k
                       [(mt: cm)
                        (mt (set-mark cm R))]
                       [(sk!: cm l k)
                        (sk! (set-mark cm R) l k)]
                       [(ifk: cm t e ρ k δ)
                        (ifk (set-mark cm R) t e ρ k δ)]
                       [(lrk: cm x xs es e ρ k δ)
                        (lrk (set-mark cm R) x xs es e ρ k δ)]
                       [(ltk: cm l x xs es xd va e ρ k δ)
                        (ltk (set-mark cm R) l x xs es xd va e ρ k δ)]
                       [(ls: cm l n es vs ρ k δ)
                        (ls (set-mark cm R) l n es vs ρ k δ)]
                       [(pfk: cm f k)
                        (pfk: (set-mark cm R) f k)])
                   #'#f))
           (define (frame k R)
             #,(if CM?
                   #'(match k
                       [(mt: cm)
                        (mt (frame-mark cm R))]
                       [(sk!: cm l k)
                        (sk! (frame-mark cm R) l k)]
                       [(ifk: cm t e ρ k δ)
                        (ifk (frame-mark cm R) t e ρ k δ)]
                       [(lrk: cm x xs es e ρ k δ)
                        (lrk (frame-mark cm R) x xs es e ρ k δ)]
                       [(ltk: cm l x xs es xd va e ρ k δ)
                        (ltk (frame-mark cm R) l x xs es xd va e ρ k δ)]
                       [(ls: cm l n es vs ρ k δ)
                        (ls (frame-mark cm R) l n es vs ρ k δ)]
                       [(pfk: cm f k)
                        (pfk (frame-mark cm R) f k)])
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
                             (for/or ([k (in-abstract-values (getter σ ka))]
                                      #:unless (hash-has-key? seen k))
                               (loop R* k))]))))))
           ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
           ;; End of continuation mark handling

           (mk-touches touches-id
                       clos: rlos: ls: lrk: ltk: ifk: sk!: pfk:
                       ast-fv list #,(zero? K) #,pushdown?)
           (splicing-syntax-parameterize
               ([yield (... #,yield-ev)]
                [touches (make-rename-transformer #'touches-id)])
             (mk-restrict-to-reachable rtrv vector-ref touches)
             (mk-restrict-to-reachable rtrh hash-ref touches)
             (splicing-syntax-parameterize
                 ([restrict-to-reachable/vector (make-rename-transformer #'rtrv)]
                  [restrict-to-reachable (make-rename-transformer #'rtrh)])
               (in-scope-of-extras
                (extra ...)
                (define-syntax do-macro (mk-do #,generators?))
                (mk-flatten-value flatten-value-fn clos: rlos: kont?)
                (splicing-syntax-parameterize ([do (make-rename-transformer #'do-macro)]
                                               [flatten-value (make-rename-transformer #'flatten-value-fn)])

                  ;; ev is special since it can mean "apply the compiled version" or
                  ;; make an actual ev state to later interpret.
                  #,@(if compiled?
                         (quasisyntax/loc stx
                           ((define-syntax (ev syn)
                              (syntax-case syn ()
                                [(_ gσ e ρ k δ)
                                 #'(tapp e #:σ gσ ρ-op ... k δ-op ...)]))
                            (define-match-expander ev: ;; inert, but introduces bindings
                              (syntax-rules () [(_ . args) (list . args)]))))
                         (quasisyntax/loc stx
                           ((mk-op-struct ev state (e ρ k δ) (e ρ-op ... k δ-op ...)
                                          expander-flags ...))))

                  (define-syntax-rule (define/ρ ρ body)
                    #,(if (zero? K)
                          #'(void)
                          #'(define ρ body)))

                  ;; No environments in 0cfa
                  (define-syntax-rule (lookup-env ρ x)
                    #,(cond [(zero? K) #'x]
                            [else #'(hash-ref ρ x (λ () (error 'lookup "Unbound var ~a" x)))]))
                  (...
                   (define-syntax (generator syn)
                     (syntax-parse syn
                       [(_ body:expr ...)
                        (syntax/loc syn
                          #,(cond [generators?
                                   (quasisyntax/loc stx
                                     (... (real-generator () body ...)))]
                                  [else
                                   (quasisyntax/loc stx
                                     (... (begin body ...)))]))])))

                  (define (inj e)
                    (define σ₀ (empty-heap))
                    (generator
                     (bind-extra-initial
                      (do (σ₀) () (yield (ev σ₀ (compile e) (hash) (mt mt-marks) '()))))))

                  (define (aval e #:prepare [prepare (?? prep-fn
                                                         (λ (e)
                                                            ;; Don't join literals when parsing for
                                                            ;; concrete evaluation.
                                                            (parameterize ([cons-limit
                                                                            #,(if (eq? K +inf.0)
                                                                                  #'+inf.0
                                                                                  #'(cons-limit))])
                                                              (define-values (e* r ps)
                                                                (parse-prog e gensym gensym))
                                                              (add-lib e* r ps gensym gensym))))])
                    #,@(syntax-parameter-value #'init-sequence)
                    (fixpoint step (inj (prepare e))))
                  ;; parameterize prim-meaning so we can use it in the definition of apply.
                  (splicing-syntax-parameterize ([prim-meaning (make-rename-transformer #'prim-meaning-def)])
                    (define-syntax mk-prims (mk-mk-prims #,compiled? #,global-σ? #,K))
                    ;; Prim-meaning is abstracted into a function, so it don't get syntactic
                    ;; context at its application point in the ap: case. For CFA2, we need to
                    ;; know the stack frame and label of the application.
                    (mk-prims prim-meaning-def compile-primop ev co ap clos rlos kont? extra ...)

                    #,@compile-def

                    ;; [Rel State State]
                    (define (step #,@(listy (and wide? (not global-σ?) #'σ)) state)
                      (match state
                        ;; Only for compiled/strict
                        #;
                        [(dr: dr-σ k a)
                        (generator
                        (do (dr-σ) ([v #:in-delay dr-σ a]) (yield (co dr-σ k v))))]
                        [(co: σ extra-ids ... k v)
                         (bind-extra (state extra-ids ...)
                          (match k
                            [(mt: cm)
                             (generator (do (σ) ([v #:in-force σ v])
                                          (yield (ans σ cm v))))]

                            ;; We need this intermediate step so that σ-∆s work.
                            ;; The above join is not merged into the store until
                            ;; after the step, and the address is needed by the call.
                            [(ls: cm l n '() v-addrs ρ a δ)
                             (define v-addr (make-intermediate-contour l n δ))
                             (define args (reverse (cons v-addr v-addrs)))
                             (generator
                              (do (σ) ([σ*-ls #:join-local-forcing σ v-addr v]
                                       [k #:in-kont σ*-ls a])
                                (yield (ap σ*-ls l (first args) (rest args) k δ))))]

                            [(ls: cm l n (cons e es) v-addrs ρ a δ)
                             (define v-addr (make-intermediate-contour l n δ))
                             (generator
                              (do (σ) ([σ*-lsn #:join-local-forcing σ v-addr v])
                                (yield (ev σ*-lsn e ρ
                                           (ls cm l (add1 n) es (cons v-addr v-addrs) ρ a δ) δ))))]

                            ;; Let is much like application, but some analyses treat let specially
                            [(ltk: cm l x '() '() x-done v-addrs e ρ a δ)
                             (define x-done* (cons x x-done))
                             (define x-addrs (for/list ([xd (in-list x-done*)])
                                               (make-var-contour l xd δ)))
                             (define/ρ ρ* (extend* ρ x-done* x-addrs))
                             (define v-addr (make-intermediate-contour l x δ))
                             (generator
                              (do (σ) ([σ*-ltk #:join-local-forcing σ v-addr v]
                                       [k* #:in-kont σ*-ltk a])
                                (yield (lt σ*-ltk e ρ* x-addrs (cons v-addr v-addrs) k* δ))))]
                            [(ltk: cm l x (cons y xs) (cons e es) x-done v-addrs b ρ a δ)
                             (define v-addr (make-intermediate-contour l x δ))
                             (generator
                              (do (σ) ([σ*-ltkn #:join-local-forcing σ v-addr v])
                                (yield (ev σ*-ltkn e ρ
                                           (ltk cm l y xs es (cons x x-done) (cons v-addr v-addrs) b ρ a δ) δ))))]

                            [(ifk: cm t e ρ a δ)
                             (generator
                              (do (σ) ([k* #:in-kont σ a]
                                       [v #:in-force σ v])
                                (yield (ev σ (if v t e) ρ k* δ))))]
                            [(lrk: cm x '() '() e ρ a δ)
                             (generator
                              (do (σ) ([σ*-lrk #:join-forcing σ (lookup-env ρ x) v]
                                       [k* #:in-kont σ*-lrk a])
                                (yield (ev σ*-lrk e ρ k* δ))))]
                            [(lrk: cm x (cons y xs) (cons e es) b ρ a δ)
                             (generator
                              (do (σ) ([σ*-lrkn #:join-forcing σ (lookup-env ρ x) v])
                                (yield (ev σ*-lrkn e ρ (lrk cm y xs es b ρ a δ) δ))))]
                            [(sk!: cm l a)
                             (generator
                              (do (σ) ([σ*-sk! #:join-forcing σ l v]
                                       [k* #:in-kont σ*-sk! a])
                                (yield (co σ*-sk! k* (void)))))]

                            [(pfk: cm fallback a)
                             (generator
                              (set-ebox! fallback v) ;; haxxx
                              (do (σ) ([k* #:in-kont σ a])
                                (yield (co σ k* v))))]
                            [_ (error 'step "Bad continuation ~a" k)]))]

                        [(lt: σ extra-ids ... e ρ x-addrs v-addrs k δ)
                         (bind-extra (state extra-ids ...)
                                     (generator
                                      (do (σ) ([σ* #:alias* σ x-addrs v-addrs])
                                        (yield (ev σ* e ρ k δ)))))]

                        [(ap: σ extra-ids ... l fn-addr arg-addrs k δ)
                         (bind-extra (state extra-ids ...)
                                     (generator
                                      (do (σ) ([f #:in-get σ fn-addr])
                                        (yield (call σ l f arg-addrs k δ)))))]

                        [(call: σ extra-ids ... l f arg-addrs k δ)
                         (bind-extra (state extra-ids ...)
                          (generator
                           (do (σ) ()
                             (match-function f
                              [(clos: xs e ρ)
                               (define xn (length xs))
                               (define an (length arg-addrs))
                               (cond [(= xn an)
                                      (do (σ)
                                          ([(ρ* σ*-clos δ*) #:bind ρ σ l δ xs arg-addrs])
                                        (yield (ev σ*-clos e (restrict-to-set ρ* (ast-fv e)) k δ*)))]
                                     ;; Yield the same state to signal "stuckness".
                                     [else
                                      (arity-error f l xn an (map (λ (a) (getter σ a)) arg-addrs))
                                      (yield (call σ l f arg-addrs k δ))])]
                              [(rlos: xs r e ρ)
                               (define xn (length xs))
                               (define an (length arg-addrs))
                               (cond [(<= xn an)
                                      (do (σ)
                                          ([(ρ* σ*-clos δ*) #:bind-rest ρ σ l δ xs r arg-addrs])
                                        (yield (ev σ*-clos e (restrict-to-set ρ* (ast-fv e)) k δ*)))]
                                     ;; Yield the same state to signal "stuckness".
                                     [else
                                      (arity-error f l (arity-at-least xn) an (map (λ (a) (getter σ a)) arg-addrs))
                                      (yield (call σ l f arg-addrs k δ))])]
                              [(primop o fallback _)
                               (tapp prim-meaning o (eunbox fallback) #f l δ-op ... k arg-addrs)]
                              [(? kont? k)
                               ;; continuations only get one argument.
                               (cond [(and (pair? arg-addrs) (null? (cdr arg-addrs)))
                                      (do (σ) ([v #:in-delay σ (car arg-addrs)])
                                        (yield (co σ k v)))]
                                     [else
                                      (cont-arity-error (length arg-addrs) f l)
                                      (yield (call σ l f arg-addrs k δ))])]
                              [(== ●) (=> fail)
                               (log-debug "implement ●-call")
                               (fail)]
                              [_
                               (non-function-error f)
                               (yield (call σ l f arg-addrs k δ))]))))]

                        ;; this code is dead when running compiled code.
                        ;; ev states shouldn't need to step "extra" components.
                        [(ev: σ extra-ids ... e ρ k δ)
                         (bind-extra (state extra-ids ...)
                                     #,(if compiled?
                                           #'(generator (do (σ) () (yield (ev σ e ρ k δ))))
                                           eval))]

                        [(ans: σ extra-ids ... cm v)
                         (bind-extra (state extra-ids ...)
                                     (generator (do (σ) () (yield (ans σ cm v)))))]

                        [_ (error 'step "Bad state ~a" state)])))

#;
                    (trace step)

                  )))))))]))
