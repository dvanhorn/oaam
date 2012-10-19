#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt"
         "env.rkt" "primitives.rkt" "parse.rkt"
         "notation.rkt"
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax)
         racket/stxparam
         racket/splicing
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

(begin-for-syntax
 (define-syntax-rule (implies ante concl) (if ante concl #t)))
(define-syntax (mk-analysis stx)
  (syntax-parse stx
    [(_ (~or ;; analysis parameters
         (~optional (~seq #:fixpoint fixpoint:expr)
                    #:defaults ([fixpoint #'fix]))
         (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
         (~once (~seq #:ans ans:id)) ;; name the answer struct to use/provide
         ;; Analysis strategies flags (requires the right parameters too)
         (~optional (~and #:compiled compiled?))
         (~optional (~and #:pre-alloc pre-alloc?))
         (~optional (~and #:σ-∆s σ-∆s?))
         (~optional (~and #:σ-passing σ-passing?))
         (~optional (~and #:wide wide?))
         (~optional (~or (~and (~seq #:kcfa k-nat-or-∞)
                               (~bind [K (syntax-e #'k-nat-or-∞)]))
                         (~and #:1cfa (~bind [K 1])))
                    #:defaults ([K 0]))
         (~optional (~or (~and #:generators generators?)
                         (~and #:set-monad set-monad?)
                         (~and #:imperative imperative?)))) ...)
     #:do [(define-syntax-rule (given kw) (syntax? (attribute kw)))
           (define global-σ?
             (and (given wide?)
                  (or (given pre-alloc?) (given imperative?))))
           (define σ-threading? (or (given σ-passing?) (given σ-∆s?)))
           (define c-passing? (given set-monad?))]
     #:fail-unless (implies (attribute pre-alloc?) (attribute wide?))
     "Cannot preallocate narrow stores."
     #:fail-unless (implies (given σ-∆s?) (given wide?))
     "Store deltas and narrow stores are antithetical."
     #:fail-when (and global-σ? (given σ-∆s?))
     "Pre-allocation and store deltas are antithetical." ;; not really, just silly
     #:fail-unless (or (given fixpoint) (given set-monad?))
     "Cannot use a general fixpoint for step function that doesn't return sets."
     #:fail-when (and (given σ-passing?) global-σ?)
     "Cannot use store passing with a global store"
     (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                    (if (zero? (attribute K)) #'(() () ()) #'((ρ) (δ) (l)))]
                   [ev: (format-id #'ev "~a:" #'ev)]
                   [ans: (format-id #'ans "~a:" #'ans)]
                   [ev #'ev]
                   ;; represent σ explicitly in all states?
                   [(σ-op ...) (if (given wide?) #'() #'(σ))]
                   ;; explicitly pass σ/∆ to compiled forms?
                   [(σ-gop ...) (if (or σ-threading? (not (given wide?))) #'(σ) #'())]
                   ;; If σ not part of state and not global, it is passed
                   ;; in as (cons σ state), so expand accordingly.
                   [(expander-flags ...)
                    (cond [(and (attribute wide?) (not global-σ?))
                           #'(#:expander #:with-first-cons)]
                          [else #'()])])
       (define-values (pass-yield-to-ev yield-ev)
         (if (attribute compiled?)
             (values #'(...
                        (λ (syn) (syntax-parse syn #:literals (ev)
                                   [(_ (ev args:expr ...))
                                    (syntax/loc syn (ev args ... real-yield))]
                                   [(_ e:expr) (syntax/loc syn (real-yield e))])))
                      #'(...
                         (λ (syn)
                           (syntax-parse syn #:literals (ev)
                             [(_ (ev args:expr ...)) (syntax/loc syn (ev args ...))]
                             [(_ e:expr) (syntax/loc syn (yield-meaning e))]))))
             (values #'(syntax-rules () [(_ e) (yield-meaning e)])
                     #'(syntax-rules () [(_ e) (yield-meaning e)]))))

       (define eval ;; what does ev mean?
         (syntax/loc stx
           (match e
             [(var l x)
              (λ% (σ ρ k δ yield)
                  (do (σ) ([v (delay σ (lookup-env ρ x))])
                    (yield (co σ k v))))]
             [(datum l d) (λ% (σ ρ k δ yield) (do (σ) () (yield (co σ k d))))]
             [(primr l which)
              (define p (primop which))
              (λ% (σ ρ k δ yield) (do (σ) () (yield (co σ k p))))]
             [(lam l x e)
              (define c (compile e))
              (λ% (σ ρ k δ yield) (do (σ) () (yield (co σ k (clos x c ρ)))))]
             [(lrc l xs es b)
              (define c (compile (first es)))
              (define cs (map compile (rest es)))
              (define cb (compile b))
              (define x (first xs))
              (define xs* (rest xs))
              (define ss (map (λ _ ∅) xs))
              (λ% (σ ρ k δ yield)
                  (define as (map (λ (x) (make-var-contour x δ)) xs))
                  (define/ρ ρ* (extend* ρ xs as))
                  (do (σ) ([(σ0 a) #:push σ l δ k]
                           [σ* #:join* σ0 as ss])
                    (yield (ev σ* c ρ* (lrk x xs* cs cb ρ* a δ) δ))))]
             [(app l e es)
              (define c (compile e))
              (define cs (map compile es))
              (λ% (σ ρ k δ yield)
                  (do (σ) ([(σ* a) #:push σ l δ k])
                    (yield (ev σ* c ρ (ls l 0 cs '() ρ a δ) δ))))]
             [(ife l e0 e1 e2)
              (define c0 (compile e0))
              (define c1 (compile e1))
              (define c2 (compile e2))
              (λ% (σ ρ k δ yield)
                  (do (σ) ([(σ* a) #:push σ l δ k])
                    (yield (ev σ* c0 ρ (ifk c1 c2 ρ a δ) δ))))]
             [(st! l x e)
              (define c (compile e))
              (λ% (σ ρ k δ yield)
                  (do (σ) ([(σ* a) #:push σ l δ k])
                    (yield (ev σ* c ρ (sk! (lookup-env ρ x) a) δ))))]
             [(primr l which) (define p (primop which))
              (λ% (σ ρ k δ yield) (do (σ) () (yield (co σ k p))))])))

       (define compile-def
         (if (attribute compiled?)
             (quasisyntax/loc stx
               ((...
                 (define-syntax-rule (λ% (σ ρ k δ yield) body ...)
                  #,(init-top-σ #f (given σ-∆s?)
                     #'σ
                     (init-target-cs
                     #f
                     c-passing?
                     (cond [(attribute generators?)
                            (quasisyntax/loc stx
                              (λ (σ-gop ... ρ-op ... k δ-op ... yield)
                                 (...
                                  (syntax-parameterize ([yield (... #,pass-yield-to-ev)]
                                                        [target-σ (make-rename-transformer #'σ)])
                                    body ...))))]
                           [else
                            (quasisyntax/loc stx
                              (λ (σ-gop ... ρ-op ... k δ-op ...)
                                 (...
                                  (syntax-parameterize ([yield (... #,yield-ev)]
                                                        [target-σ (make-rename-transformer #'σ)])
                                    body ...))))])))))
                (define (compile e) #,eval)))
             ;; brittle, since other identifiers must be the same in ev:
             (quasisyntax/loc stx
               ((... (define-syntax-rule (λ% (σ ρ k δ yield) body ...)
                       (generator body ...)))
                (define compile values)))))

       (quasisyntax/loc stx
         (begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct co (σ k v) (σ-op ... k v) expander-flags ...)
           (mk-op-struct ans (σ v) (σ-op ... v) expander-flags ...)
           (mk-op-struct ap (σ l fn-addr v-addrs k δ)
                         (σ-op ... l fn-addr v-addrs k δ-op ...)
                         expander-flags ...)
           (struct mt () #:prefab)
           (struct sk! (x k) #:prefab)
           (struct primop (which) #:prefab)
           (mk-op-struct ifk (t e ρ k δ) (t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (x xs es e ρ k δ) (x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (l n es vs ρ k δ) (l n es vs ρ-op ... k δ-op ...))
           (mk-op-struct clos (x e ρ) (x e ρ-op ...))
           (splicing-syntax-parameterize ([target-σ? #,σ-threading?]
                                          [target-cs? #,c-passing?])
           (define-syntax do-macro
             (mk-do #,(given σ-∆s?)
                    #,c-passing?
                    #,global-σ?
                    #,(given generators?)))
           (splicing-syntax-parameterize ([do (make-rename-transformer #'do-macro)])

           ;; ev is special since it can mean "apply the compiled version" or
           ;; make an actual ev state to later interpret.
           #,@(if (given compiled?)
                  (quasisyntax/loc stx
                    ((define-syntax ev
                       (syntax-rules ()
                         ;; σ only optional if it's global (wide, imperative/prealloc)
                         [(_ σ e ρ k δ yield) (e σ-gop ... ρ-op ... k δ-op ... yield)]
                         [(_ σ e ρ k δ) (e σ-gop ... ρ-op ... k δ-op ...)]))
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
                   #,(init-target-cs
                      #f
                      c-passing?
                      (cond [(given generators?)
                             (quasisyntax/loc stx
                               (...
                                (syntax-parameterize ([yield (... #,pass-yield-to-ev)])
                                  (real-generator () body ... 'done))))]
                            [else
                             (quasisyntax/loc stx
                               (...
                                (syntax-parameterize ([yield (... #,yield-ev)])
                                  (begin (continue) body ...))))])))])))

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
             (syntax-parameterize ([target-σ (λ (stx) #'(hash))])
               (generator
                (yield
                 (ev (hash) ;; store is a hash unless it's preallocated and global, thus dropped
                     (compile e)
                     (hash) ;; no meaning for free variables
                     (mt)   ;; starting contour is empty
                     ε)))))

           (define (aval e) (fixpoint step (inj e)))

           #,@compile-def

           (mk-prims prim-meaning)
           ;; [Rel State State]
           (define (step state)
             (match state
               [(co: σ k v)
                (syntax-parameterize ([target-σ (make-rename-transformer #'σ)]
                                      [top-σ (make-rename-transformer #'σ)])
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
                       (do (σ) ([σ* #:join σ v-addr (force σ v)]
                                [k (getter σ* a)])
                         (yield (ap σ* l (first args) (rest args) k δ))))]

                  [(ls: l n (list-rest e es) v-addrs ρ a δ)
                   (define v-addr (make-var-contour (cons l n) δ))
                   (generator
                       (do (σ) ([σ* #:join σ v-addr (force σ v)])
                         (yield (ev σ* e ρ
                                    (ls l (add1 n) es (cons v-addr v-addrs) ρ a δ) δ))))]
                  [(ifk: t e ρ a δ)
                   (generator
                       (do (σ) ([k* (getter σ a)]
                                [v (force σ v)])
                         (yield (ev σ (if v t e) ρ k* δ))))]
                  [(lrk: x '() '() e ρ a δ)
                   (generator
                       (do (σ) ([σ* #:join σ (lookup-env ρ x) (force σ v)]
                                [k* (getter σ* a)])
                         (yield (ev σ* e ρ k* δ))))]
                  [(lrk: x (cons y xs) (cons e es) b ρ a δ)
                   (generator
                       (do (σ) ([σ* #:join σ (lookup-env ρ x) (force σ v)])
                         (yield (ev σ* e ρ (lrk y xs es b ρ a δ) δ))))]
                  [(sk! l a)
                   (generator
                       (do (σ) ([σ* #:join σ l (force σ v)]
                                [k* (getter σ* a)])
                         (yield (co σ* k* (void)))))]))]

               ;; v is not a value here. It is an address.
               [(ap: σ l fn-addr arg-addrs k δ)
                (syntax-parameterize ([target-σ (make-rename-transformer #'σ)]
                                      [top-σ (make-rename-transformer #'σ)])
                (generator
                    (do (σ) ([f (getter σ fn-addr)])
                      (match f
                        [(clos: xs e ρ)
                         (cond [(= (length xs) (length arg-addrs))
                                (do (σ)
                                    ([(ρ* σ* δ*) #:bind ρ σ l δ xs arg-addrs])
                                  (yield (ev σ* e ρ* k δ*)))]
                               ;; Yield the same state to signal "stuckness".
                               [else
                                (printf "Arity error on ~a~%" f)
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
                         (printf "Stuck (non-function) ~a~%" f)
                         (yield (ap σ l fn-addr arg-addrs k δ))]))))]

               ;; this code is dead when running compiled code.
               [(ev: σ e ρ k δ)
                (syntax-parameterize ([target-σ (make-rename-transformer #'σ)]
                                      [top-σ (make-rename-transformer #'σ)])
                  (unless (hash? σ)
                    (error 'step "Bad ev σ: ~a~%" σ))
                  #,(if (given compiled?)
                        #'(generator (yield (ev σ e ρ k δ)))
                        eval))]

               [(ans: σ v)
                (syntax-parameterize ([top-σ (make-rename-transformer #'σ)]
                                      [target-σ (make-rename-transformer #'σ)])
                  (generator (yield (ans σ v))))]
               [_ (error 'step "What? ~a" state)]))
;;           (trace step)
           )))))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; That concludes the framework. See kcfa-instantiations.rkt for common
;; definitions for the framework parameters and a few instantiations.
;; These aren't in the framework themselves, even though the flags are
;; there. The flags are for setting up the binding structure that these
;; different strategies utilize.
;; One can imagine other parameterizations with the same binding structures.

