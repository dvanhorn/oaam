#lang racket
(require "ast.rkt"
         (for-syntax syntax/parse racket/syntax racket/match)
         (rename-in racket/generator
                    [yield real-yield] ;; I'll take those, thank you.
                    [generator real-generator])
         racket/stxparam)
(provide yield (for-syntax mk-mk-analysis) (struct-out addr) (struct-out ans))


(define-syntax-parameter yield
  (λ (stx) (raise-syntax-error #f "Must be within the context of a generator" stx)))

(struct addr (a) #:prefab)
(struct ans (v) #:prefab)

(begin-for-syntax
(define-syntax-rule (implies ante concl) (if ante concl #t))

(define ((mk-mk-analysis do-body-meaning do-loop-meaning yield-meaning) stx)
   (syntax-parse stx
     [(_ (~or ;; analysis parameters
          (~once (~seq #:bind-join-one bind-join-one:id))
          (~once (~seq #:bind-join bind-join:id))
          (~once (~seq #:bind-push bind-push:id))
          (~once (~seq #:tick tick:id))
          (~once (~seq #:get-cont get-cont:id))
          (~once (~seq #:force force:id))
          (~once (~seq #:delay delay:id))
          (~once (~seq #:widen widen:id))
          (~once (~seq #:make-var-contour make-var-contour:id))
          (~once (~seq #:fixpoint fixpoint:expr))
          (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
          ;; Define the compiler? With what name?
          ;; Analysis strategies flags (requires the right parameters too)
          (~optional (~and #:compiled compiled?))
          (~optional (~and #:pre-alloc pre-alloc?))
          (~optional (~and #:σ-∆s σ-∆s?))
          (~optional (~and #:wide (~bind [(σ-op 1) '()] [wide? #t]))
                     #:defaults ([(σ-op 1) (list #'σ)] [wide? #f]))
          (~optional (~or (~and (~seq #:kcfa k-nat:nat)
                                (~bind [K (syntax-e #'k-nat)]))
                          (~and #:1cfa (~bind [K 1])))
                     #:defaults ([K 0]))
          (~optional (~or (~and #:generators generators?)
                          (~and #:set-monad set-monad?)
                          (~and #:imperative imperative?)))) ...)
      #:fail-unless (implies (attribute pre-alloc?) (attribute wide?))
      "Cannot preallocate narrow stores."
      #:fail-unless (implies (attribute σ-∆s?) (attribute wide?))
      "Narrow stores and store deltas are antithetical."
      #:fail-when (and (attribute pre-alloc?) (attribute σ-∆s?))
      "Pre-allocation and store deltas are antithetical."
      #:fail-unless (or (attribute fixpoint) (attribute set-monad?))
      "Cannot use a general fixpoint for step function that doesn't return sets."
      (define global-σ?
        (and (attribute wide?)
             (or (attribute pre-alloc?) (attribute imperative?))))
      (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                     (if (zero? (attribute K)) #'(() () ()) #'((ρ) (δ) (l)))]
                    [(σ-cop ...) (if global-σ? #'() #'(σ))]
                    [(expander-flags ...)
                     (if (and (attribute wide?) (not global-σ?))
                         #'(#:expander #:with-first-cons)
                         #'())])
        (define eval ;; what does ev mean?
          (syntax/loc stx
            (match e
              [(var l x)
               (λ% (σ ρ k δ yield)
                   (do (σ)
                       ([v (delay σ (lookup-env ρ x))])
                     (yield (co σ k v))))]
              [(num l n)   (λ% (σ ρ k δ yield) (yield (co σ k n)))]
              [(bln l b)   (λ% (σ ρ k δ yield) (yield (co σ k b)))]
              [(lam l x e)
               (define c (compile e))
               (λ% (σ ρ k δ yield) (yield (co σ k (clos x c ρ))))]
              [(rec f (lam l x e))
               (define c (compile e))
               (λ% (σ ρ k δ yield) (yield (co σ k (rlos f x c ρ))))]
              [(app l e0 e1)
               (define c0 (compile e0))
               (define c1 (compile e1))
               (λ% (σ ρ k δ yield)
                   (do (σ)
                       ([(σ* a) #:push σ δ l ρ k])
                     (yield (ev σ* c0 ρ δ (ar c1 ρ δ l a)))))]
              [(ife l e0 e1 e2)
               (define c0 (compile e0))
               (define c1 (compile e1))
               (define c2 (compile e2))
               (λ% (σ ρ k δ yield)
                   (do (σ)
                       ([(σ* a) #:push σ δ l ρ k])
                     (yield (ev σ* c0 ρ δ (ifk c1 c2 ρ δ a)))))]
              [(1op l o e)
               (define c (compile e))
               (λ% (σ ρ k δ yield)
                   (do (σ)
                       ([(σ* a) #:push σ δ l ρ k])
                     (yield (ev σ* c ρ δ (1opk o δ a)))))]
              [(2op l o e0 e1)
               (define c0 (compile e0))
               (define c1 (compile e1))
               (λ% (σ ρ k δ yield)
                   (do (σ)
                       ([(σ* a) #:push σ δ l ρ k])
                     (yield (ev σ* c0 ρ δ (2opak o c1 ρ δ a)))))]
              [_ (error 'compile "Bad ~a" e)])))

        (define compile-def
          (if (attribute compiled?)
              #`((define-syntax-rule (... (λ% (σ ρ k δ yield) body ...))
                   #,(cond [(attribute generators?)
                            (syntax/loc stx
                              (λ (σ-cop ... ρ-op ... k δ-op ... dummy)
                                 (...
                                  (syntax-parameterize ([yield (pass-given-yield-to-ev #'dummy)])
                                    (begin body ...)))))]
                           [else
                            (syntax/loc stx
                              (λ (σ-cop ... ρ-op ... k δ-op ...)
                                 (...
                                  (syntax-parameterize ([yield (make-rename-transformer #'yield-ev)])
                                    (begin body ...)))))]))
                 (define (compile e)
                   #,eval))
              #`((... (define-syntax-rule (λ% (σ ρ k δ yield) body ...)
                        (generator body ...)))
                 (define (compile e) e))))

        #`(begin ;; specialize representation given that 0cfa and widening need less
            (mk-op-struct ap (σ fun arg δ l k) (σ-op ... fun arg δ-op ... l-op ... k) expander-flags ...)
            (mk-op-struct co (σ k v) (σ-op ... k v) expander-flags ...)
            (mk-op-struct ap-op (σ o vs k) (σ-op ... o vs k) expander-flags ...)
            (mk-op-struct ar (e ρ δ l k) (e ρ-op ... δ-op ... l-op ... k))
            (mk-op-struct fn (v δ l k) (v δ-op ... l-op ... k))
            (mk-op-struct ifk (t e ρ δ k) (t e ρ-op ... δ-op ... k))
            (mk-op-struct 1opk (o δ k) (o δ-op ... k))
            (mk-op-struct 2opak (o e ρ δ k) (o e ρ-op ... δ-op ... k))
            (mk-op-struct 2opfk (o v δ k) (o v δ-op ... k))
            (mk-op-struct clos (x e ρ) (x e ρ-op ...))
            (mk-op-struct rlos (f x e ρ) (f x e ρ-op ...))

            ;; ev is special since it can mean "apply the compiled version" or
            ;; make an actual ev state to later interpret.
            #,@(if (attribute compiled?)
                   #`((define-syntax ev
                        (syntax-rules ()
                          ;; σ only optional if it's global (wide, imperative/prealloc)
                          [(_ σ e ρ δ k yield) (e σ-cop ... ρ-op ... δ-op ... k yield)]
                          [(_ σ e ρ δ k) (e σ-cop ... ρ-op ... δ-op ... k)]))
                      (define-match-expander ev:
                        (syntax-rules () [(_ σ e ρ δ k) #f]))
                      (...
                       (begin
                         (define-syntax (pass-yield-to-ev syn) ;; real generators
                           (syntax-parse syn #:literals (ev)
                             [(_ (ev args:expr ...))
                              (syntax/loc syn
                                (ev args ... real-yield))]
                             [(_ e:expr) (syntax/loc syn (real-yield e))]))
                         ;; Need to not capture the unquote-syntaxes here.
                         #,#'(...
                         (define-for-syntax ((pass-given-yield-to-ev the-yield) syn) ;; real generators
                           (syntax-parse syn #:literals (ev)
                             [(_ (ev args:expr ...))
                              (quasisyntax/loc syn
                                (ev args ... #,the-yield))]
                             [(_ e:expr) (quasisyntax/loc syn
                                           (#,the-yield e))])))
                         (define-syntax (yield-ev syn)
                           (syntax-parse syn #:literals (ev)
                             [(_ (ev args:expr ...)) (syntax/loc syn
                                                       (ev args ...))]
                             [(_ e:expr) (syntax/loc syn
                                           #,(yield-meaning #'e))])))))
                   #`((mk-op-struct ev (σ e ρ δ k) (σ-op ... e ρ-op ... δ-op ... k))
                      (define-syntax pass-yield-to-ev (syntax-rules () [(_ e) #,(yield-meaning #'e)]))
                      (define-syntax yield-ev (syntax-rules () [(_ e) #,(yield-meaning #'e)]))))

            ;; No environments in 0cfa
            (define-syntax-rule (lookup-env ρ x)
              #,(cond [(zero? (attribute K)) #'x]
                      [else #'(hash-ref ρ x (λ () (error 'lookup "Unbound var ~a" x)))]))
            ;; yield colludes with ev to make compiled and
            ;; other strategies look the same
            (define-syntax-rule (... (generator body ...))
               #,(cond [(attribute generators?)
                        (syntax/loc stx
                          (... (syntax-parameterize ([yield (make-rename-transformer #'pass-yield-to-ev)])
                                 (real-generator () body ... 'done))))]
                       [else
                        (syntax/loc stx
                          (... (syntax-parameterize ([yield (make-rename-transformer #'yield-ev)])
                                 (begin (void) body ...))))]))

            (...
             (define-syntax (do stx)
               (define-syntax-class (join-clause prev-σ replace-v outer-σ body)
                 #:attributes (clause new-σ val)
                 (pattern [σ*:id (~or (~and #:join-one (~bind [bindf #'bind-join-one]))
                                      (~and #:join (~bind [bindf #'bind-join]))) σ:expr a:expr v:expr]
                          #:with new-σ #'σ* #:attr val #'v
                          #:attr clause
                          (λ (rest)
                             #`(bindf (σ* σ a #,(or replace-v #'v)) #,(rest #'σ* outer-σ body))))
                 (pattern [(σ*:id a*:id) #:push σ δ l ρ k]
                          #:with new-σ #'σ* #:attr val #f
                          #:attr clause
                          (λ (rest)
                             #`(bind-push (σ* a* σ δ l ρ k) #,(rest #'σ* outer-σ body)))))
               ;; A terrible binding pattern is necessary for store deltas. We /hoist/
               ;; the values that are used in join so they are in scope of the real σ.
               (define-splicing-syntax-class (join-clauses maybe-prev-σ outer-σ body)
                 #:attributes (clauses (ids 1) (vs 1) (prev-σs 1))
                 (pattern (~seq) #:attr clauses '() #:attr (ids 1) '() #:attr (vs 1) '()
                          #:attr (prev-σs 1) '())
                 (pattern (~seq (~bind [new-id (generate-temporary)])
                           (~var join (join-clause (or maybe-prev-σ outer-σ)
                                                   (and #,(syntax? (attribute σ-∆s?)) #'new-id)
                                                   outer-σ body))
                           (~var joins (join-clauses (attribute join.new-σ) outer-σ body)))
                          #:attr clauses (cons (attribute join.clause) (attribute joins.clauses))

                          #:attr (ids 1) (let ([v (attribute join.val)]
                                               [ids* (attribute joins.ids)])
                                       (if v (cons #'new-id ids*) ids*))
                          #:attr (vs 1) (let ([v (attribute join.val)]
                                              [vs* (attribute joins.vs)])
                                       (if v (cons v vs*) vs*))
                          #:attr (prev-σs 1)
                          (let ([v (attribute join.val)])
                            (if v
                                (if maybe-prev-σ
                                    (cons maybe-prev-σ (attribute joins.prev-σs))
                                    (cons outer-σ (attribute joins.prev-σs)))
                                (attribute joins.prev-σs)))))
               (syntax-parse stx
                 ;; if we don't get a store via clauses, σ is the default.
                 [(~and (_ (σ:id) ([x:id e:expr] ... blob ...) body:expr)
                        (_ dk0 ([x0 e0] ... (~var joins (join-clauses #f #'σ #'body))) dk1))
                  ;; flags conflate imperative store and imperative worklist in wide case
                  ;; store-passing/store-δ-accumulation is needed if
                  ;; ¬wide or (¬pre-alloc and ¬imperative)
                  ;; ≡ ¬(wide and (pre-alloc or imperative))
                  (define binds (let loop ([j (reverse (attribute joins.clauses))]
                                           [full #,do-body-meaning])
                                  (match j
                                    [(cons fn js) (loop js (λ _ (fn full)))]
                                    [_ (full #'σ #'σ #'body)])))
                  (define hoist-binds
                    #,(if (attribute σ-∆s?)
                          (if global-σ?
                              #'(... #'([joins.ids joins.vs] ...))
                              #'(... #'([joins.ids (let ([joins.prev-σs σ]) joins.vs)] ...)))
                          #''()))
                  (#,do-loop-meaning hoist-binds binds #'σ #'([x e] ...))]
                 [(_ (σ:id) ([x:id e:expr] ... blob ...) body:expr)
                  (raise-syntax-error #f "Joins failed" stx)])))

            #,@compile-def

            ;; "Bytecode" interpreter
            ;;  State -> State^
            (define (step s)
              (match s
                [(co: σ k v)
                 (match k
                   ['mt (generator (do (σ)
                                       ([v (force σ v)])
                                     (yield (ans v))))]
                   [(ar: e ρ δ l a)
                    (generator (yield (ev σ e ρ δ (fn v δ l a))))]
                   [(fn: f δ l a)
                    (generator
                        (do (σ)
                            ([k (get-cont σ a)]
                             [f (force σ f)])
                          (yield (ap σ f v δ l k))))]
                   [(ifk: t e ρ δ a)
                    (generator
                        (do (σ)
                            ([k (get-cont σ a)]
                             [v (force σ v)])
                          (yield (ev σ (if v t e) ρ δ k))))]

                   [(1opk: o δ a)
                    (generator
                        (do (σ)
                            ([k (get-cont σ a)]
                             [v (force σ v)])
                          (yield (ap-op σ o (list v) k))))]
                   [(2opak: o e ρ δ a)
                    (generator (yield (ev σ e ρ δ (2opfk o v δ a))))]

                   [(2opfk: o u δ a)
                    (generator
                        (do (σ)
                            ([k (get-cont σ a)]
                             [v (force σ v)]
                             [u (force σ u)])
                          (yield (ap-op σ o (list v u) k))))]
                   [_ (error 'step "Bad ~a" k)])]

                [(ap: σ fun v δ l k)
                 (match fun
                   [(clos: x e ρ)
                    (define x-addr (make-var-contour x δ))
                    (generator
                        (do (σ)
                            ([σ* #:join σ x-addr (force σ v)])
                          (yield (ev σ* e (extend ρ x x-addr) (tick δ l) k))))]
                   [(rlos: f x e ρ)
                    (define f-addr (make-var-contour f δ))
                    (define x-addr (make-var-contour x δ))
                    (generator
                        (do (σ)
                            ([σ* #:join-one σ f-addr fun]
                             [σ* #:join σ* x-addr (force σ* v)])
                          (yield (ev σ* e (extend (extend ρ x x-addr) f f-addr) (tick δ l) k))))]
                   ;; Anything else is stuck
                   [_ (generator)])]

                [(ap-op: σ o vs k)
                 (match* (o vs)
                   [('zero? (list (? number? n))) (generator (yield (co σ k (zero? n))))]
                   [('sub1 (list (? number? n)))  (generator (yield (co σ k (widen (sub1 n)))))]
                   [('add1 (list (? number? n)))  (generator (yield (co σ k (widen (add1 n)))))]
                   [('zero? (list 'number))
                    (generator (do (σ)
                                   ([b (in-list '(#t #f))])
                                 (yield (co σ k b))))]
                   [('sub1 (list 'number)) (generator (yield (co σ k 'number)))]
                   [('* (list (? number? n) (? number? m)))
                    (generator (yield (co σ k (widen (* m n)))))]
                   [('* (list (? number? n) 'number))
                    (generator (yield (co σ k 'number)))]
                   [('* (list 'number 'number))
                    (generator (yield (co σ k 'number)))]
                   ;; Anything else is stuck
                   [(_ _) (void)])]

                ;; Unreachable if compiled. However, avoid code duplication.
                [(ev: σ e ρ δ k) #,(if (attribute compiled?) #'(void) eval)]

                [s (generator)]))

            (define (inj e)
              (generator
                (yield
                  (ev (hash) ;; store is a hash unless it's preallocated and global, thus dropped
                      (compile e)
                      (hash) ;; no meaning for free variables
                      '()    ;; starting contour is empty
                      'mt))))

            (define (aval e)
              #,(cond [(attribute fixpoint)
                       (syntax/loc stx (fixpoint step (inj e)))]
                      [else ;; must be in set monad
                       (syntax/loc stx (fix step (inj e)))]))))])))

;; Make a struct that looks like it has all the fields given, but really
;; only has the subfields.
(define-syntax (mk-op-struct stx)
  (syntax-parse stx
    [(_ name:id (fields:id ...) (subfields:id ...)
        (~bind [container (format-id #'name "~a-container" #'name)]
               [name: (format-id #'name "~a:" #'name)])
        (~optional
         (~seq #:expander
               (~or (~and #:with-first-cons
                          (~bind [expander
                                  #`(syntax-rules ()
                                      [(_ σ #,@(cdr (syntax->list #'(fields ...))))
                                       (cons σ (container subfields ...))])]))
                    expander:expr))
         #:defaults ([expander
                      #'(syntax-rules ()
                          [(_ fields ...) (container subfields ...)])])))
     #:fail-unless (for/and ([s (in-list (syntax->list #'(subfields ...)))])
                     (for/or ([f (in-list (syntax->list #'(fields ...)))])
                       (free-identifier=? f s)))
     "Subfields should be contained in fields list."
     #'(begin (struct container (subfields ...) #:prefab)
              (define-syntax-rule (name fields ...) (container subfields ...))
              (define-match-expander name: expander))]
    [(_ name:id (fields:id ...) . rest) (raise-syntax-error #f "Expected subfields" stx)]
    [(_ name:id . rest) (raise-syntax-error #f "Expected fields and subfields" stx)]
    [(_ . rest) (raise-syntax-error #f "Expected name, fields and subfields" stx)]))
