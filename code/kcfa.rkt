#lang racket

(require "ast.rkt" "fix.rkt" "data.rkt"
         "env.rkt"
         "notation.rkt" "primitives.rkt" "parse.rkt"
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         (for-syntax syntax/parse racket/syntax)
         racket/stxparam
         racket/splicing)

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
         ;; Define the compiler? With what name?
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
     #:fail-unless (implies (attribute pre-alloc?) (attribute wide?))
     "Cannot preallocate narrow stores."
     #:fail-unless (implies (attribute σ-∆s?) (attribute wide?))
     "Store deltas and narrow stores are antithetical."
     #:fail-when (and (attribute pre-alloc?) (attribute σ-∆s?))
     "Pre-allocation and store deltas are antithetical."
     #:fail-unless (or (attribute fixpoint) (attribute set-monad?))
     "Cannot use a general fixpoint for step function that doesn't return sets."
     #:do [(define global-σ?
             (and (attribute wide?)
                  (syntax?
                   (or (attribute pre-alloc?) (attribute imperative?)))))]
     #:fail-when (and (attribute σ-passing?) global-σ?)
     "Cannot use store passing with a global store"
     (define σ-threading?
       (or (syntax? (attribute σ-passing?)) (syntax? (attribute σ-∆s?))))
     (define c-passing? (syntax? (attribute set-monad?)))
     (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                    (if (zero? (attribute K))
                        #'(() () ())
                        #'((ρ) (δ) (l)))]
                   [ev: (format-id #'ev "~a:" #'ev)]
                   [ans: (format-id #'ans "~a:" #'ans)]
                   [ev #'ev]
                   ;; represent σ explicitly in all states?
                   [(σ-op ...) (if (or global-σ? (attribute wide?)) #'() #'(σ))]
                   ;; explicitly pass σ/∆ to compiled forms?
                   [(σ-gop ...) (if σ-threading? #'(σ) #'())]
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
                             [(_ (ev args:expr ...)) #'(ev args ...)]
                             [(_ e:expr) #'(yield-meaning e)]))))
             (values #'(syntax-parser [(_ e) #'(yield-meaning e)])
                     #'(syntax-parser [(_ e) #'(yield-meaning e)]))))

       (define eval ;; what does ev mean?
         #'(match e
             [(var l x)
              (λ% (σ ρ k δ yield)
                  (do (σ) ([v (delay σ (lookup-env ρ x))])
                    (yield (co σ k v))))]
             [(datum l d) (λ% (σ ρ k δ yield) (yield (co σ k d)))]
             [(primr l which)
              (define p (primop which))
              (λ% (σ ρ k δ yield) (yield (co σ k p)))]
             [(lam l x e)
              (define c (compile e))
              (λ% (σ ρ k δ yield) (yield (co σ k (clos x c ρ))))]
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
                    (yield (ev σ* c ρ (ls l cs '() ρ a δ) δ))))]
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
              (λ% (σ* ρ k δ yield) (yield (co σ* k p)))]))

       (define compile-def
         (if (attribute compiled?)
             #`((...
                 (define-syntax-rule (λ% (σ ρ k δ yield) body ...)
                  #,((init-target-cs c-passing?)
                     (cond [(attribute generators?)
                            #`(λ (σ-gop ... ρ-op ... k δ-op ... yield)
                                 (...
                                  (syntax-parameterize ([yield (... #,pass-yield-to-ev)]
                                                        [target-σ (make-rename-transformer #'σ)])
                                    body ...)))]
                           [else
                            #`(λ (σ-gop ... ρ-op ... k δ-op ...)
                                 (...
                                  (syntax-parameterize ([yield (... #,yield-ev)]
                                                        [target-σ (make-rename-transformer #'σ)])
                                    body ...)))]))))
                (define (compile e) #,eval))
             #`((... (define-syntax-rule (λ% (σ ρ k δ yield) body ...)
                       (syntax-parameterize ([target-σ (make-rename-transformer #'σ)])
                         (generator body ...))))
                (define compile values))))

       #`(begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct co (σ k v) (σ-op ... k v) expander-flags ...)
           (mk-op-struct ans (σ v) (σ-op ... v) expander-flags ...)
           (struct mt () #:prefab)
           (struct sk! (x k) #:prefab)
           (struct primop (which) #:prefab)
           (mk-op-struct ifk (t e ρ k δ) (t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (x xs es e ρ k δ) (x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (l es vs ρ k δ) (l es vs ρ-op ... k δ-op ...))
           (mk-op-struct clos (x e ρ) (x e ρ-op ...))
           (splicing-syntax-parameterize ([target-σ? #,σ-threading?]
                                          [target-cs? #,c-passing?])
           (define-syntax do-macro
             (mk-do #,(syntax? (attribute σ-∆s?))
                    #,c-passing?
                    #,global-σ?
                    #,(syntax? (attribute generators?))))
           (splicing-syntax-parameterize ([do (make-rename-transformer #'do-macro)])

           ;; ev is special since it can mean "apply the compiled version" or
           ;; make an actual ev state to later interpret.
           #,@(if (attribute compiled?)
                  #`((define-syntax (ev stx)
                       (syntax-parse stx
                         ;; σ only optional if it's global (wide, imperative/prealloc)
                         [(_ σ e ρ k δ yield) #'(e σ-gop ... ρ-op ... k δ-op ... yield)]
                         [(_ σ e ρ k δ) #'(e σ-gop ... ρ-op ... k δ-op ...)]))
                     (define-match-expander ev: ;; inert
                       (syntax-rules () [(_ . args) (list . args)])))
                  #`((mk-op-struct ev (σ e ρ k δ) (σ-op ... e ρ-op ... k δ-op ...)
                                   expander-flags ...)))

            (define-syntax-rule (define/ρ ρ body)
             #,(if (zero? (attribute K))
                   #'(void)
                   #'(define ρ body)))

           ;; No environments in 0cfa
           (define-syntax-rule (lookup-env ρ x)
             #,(cond [(zero? (attribute K)) #'x]
                     [else #'(hash-ref ρ x (λ () (error 'lookup "Unbound var ~a" x)))]))
           (...
            (define-syntax generator
              (syntax-parser
                [(_ body:expr ...)
                 #'#,((init-target-cs c-passing?)
                      (cond [(attribute generators?)
                             #`(...
                                (syntax-parameterize ([yield (... #,pass-yield-to-ev)])
                                  (real-generator () body ... 'done)))]
                            [else
                             #`(...
                                (syntax-parameterize ([yield (... #,yield-ev)])
                                  (begin (continue) body ...)))]))])))

           ;; Let primitives yield single values instead of entire states.
           (define-syntax (with-prim-yield stx)
             (syntax-parse stx
               [(_ k body)
                (define yield-tr (syntax-parameter-value #'yield-meaning))
                (define new (λ (stx) (syntax-parse stx [(_ v) (yield-tr #'(yield (co target-σ k v)))])))
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
                (syntax-parameterize ([target-σ (make-rename-transformer #'σ)])
                (match k
                  [(mt) (generator (do (σ) ([v (force σ v)])
                                     (yield (ans σ v))))]

                  [(ls: l '() vs ρ a δ)
                   (define args (reverse (cons v vs)))
                   (generator
                       (do (σ) ([k (getter σ a)]
                                [f (force σ (first args))])
                         (match f
                           [(clos: xs e ρ)
                            (cond [(= (length xs) (length (rest args)))
                                   (do (σ) ([(ρ* σ* δ*) #:bind ρ σ l δ xs (rest args)])
                                       (yield (ev σ* e ρ* k δ*)))]
                                  [else (generator (yield (co σ k v)))])]
                           [(primop o)
                            (define forced (for/list ([a (in-list (rest args))])
                                             (force σ a)))
                            (with-prim-yield k
                             (do (σ) ([vs (in-set (toSetOfLists forced))])
                               (prim-meaning o σ l δ vs)))]
                           [_ (generator (yield (co σ k v)))])))]

                  [(ls: l (list-rest e es) vs ρ a δ)
                   (generator
                       (yield (ev σ e ρ (ls l es (cons v vs) ρ a δ) δ)))]
                  [(ifk: t e ρ a δ)
                   (generator
                       (do (σ) ([k (getter σ a)]
                                [v (force σ v)])
                         (yield (ev σ (if v t e) ρ k δ))))]
                  [(lrk: x '() '() e ρ a δ)
                   (generator
                       (do (σ) ([σ* #:join σ (lookup-env ρ x) (force σ v)]
                                [k (getter σ a)])
                         (yield (ev σ* e ρ k δ))))]
                  [(lrk: x (cons y xs) (cons e es) b ρ a δ)
                   (generator
                       (do (σ) ([σ* #:join σ (lookup-env ρ x) (force σ v)])
                         (yield (ev σ* e ρ (lrk y xs es b ρ a δ) δ))))]
                  [(sk! l a)
                   (generator
                       (do (σ) ([σ* #:join σ l (force σ v)]
                                [k (getter σ a)])
                         (yield (co σ* k (void)))))]))]

               ;; this code is dead when running compiled code.
               [(ev: σ e ρ k δ)
                #,(if (attribute compiled?)
                      #'(syntax-parameterize ([target-σ (make-rename-transformer #'σ)])
                          (generator (yield (ev σ e ρ k δ))))
                        eval)]

               [(ans: σ v)
                (syntax-parameterize ([target-σ (make-rename-transformer #'σ)])
                  (generator (yield (ans σ v))))]
               [_ (error 'step "What? ~a" state)]))))))]))

(define (map2-append f acc ls0 ls1)
  (let loop ([ls0 ls0] [ls1 ls1])
    (match* (ls0 ls1)
      [((cons h0 t0) (cons h1 t1))
       (cons (f h0 h1) (loop t0 t1))]
      [('() '()) acc]
      [(_ _)
       (error 'map2-append "Expected same length lists. Finished at ~a ~a"
              ls0 ls1)])))

(define-syntax-rule (bind-join-whole (σ* σ a vs) body)
  (let ([σ* (join σ a vs)]) body))
(define-syntax-rule (bind-join*-whole (σ* σ as vss) body)
  (let ([σ* (join* σ as vss)]) body))
(define-simple-macro* (bind-join-∆s (∆s* ∆s a vs) body)
  (let ([∆s* (cons (cons a vs) ∆s)]) body))
(define-simple-macro* (bind-join*-∆s (∆s* ∆s as vss) body)
  (let ([∆s* (map2-append cons ∆s as vss)]) body))

(define-for-syntax ((mk-bind K) stx)
  (syntax-case stx ()
    [(_ (ρ* σ* δ*) (ρ σ l δ xs vs) body)
     (if (zero? K)
         (syntax/loc stx
           (bind-join* (σ* σ xs (map (λ (v) (force σ v)) vs)) body))
         (quasisyntax/loc stx
           (let* ([δ* (truncate (cons l δ) #,K)]
                  [as (map (λ (x) (cons x δ*)) xs)]
                  [ρ* (extend* ρ xs as)])
             (bind-join* (σ* σ as (map (λ (v) (force σ v)) vs)) body))))]))
(define-syntax-rule (make-var-contour-0 x δ) x)
(define-syntax-rule (make-var-contour-k x δ) (cons x δ))

(define-syntax bind-0 (mk-bind 0))
(define-syntax bind-∞ (mk-bind +inf.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widen set-monad fixpoint
(define-syntax-rule (wide-step step)
  (λ (state)
     (match state
       [(cons σ cs)
        (define-values (σ* cs*)
          (for/fold ([σ* σ] [cs ∅]) ([c (in-set cs)])
            (define-values (σ** cs*) (step (cons σ c)))
            (values (join-store σ* σ**) (∪ cs* cs))))
        (set (cons σ* cs*))]
       [_ (error 'wide-step "bad output ~a~%" state)])))

(define-syntax-rule (mk-∆-fix^ name ans^?)
  (define-syntax-rule (name stepper fst)
    (let-values ([(∆ cs) fst])
     (define seen (make-hash))
     (define todo (set (cons (update ∆ (hash)) cs)))
     (let loop ()
       (cond [(∅? todo) (for/set ([(c σ) (in-hash seen)]
                                  #:when (ans^? c))
                          (cons σ c))]
             [else (define old-todo todo)
                   (set! todo ∅)
                   (for* ([σ×cs (in-set old-todo)]
                          [σ (in-value (car σ×cs))]
                          [c (in-set (cdr σ×cs))]
                          [last-σ (in-value (hash-ref seen c (hash)))]
                          #:unless (equal? last-σ σ))
                     ;; This state's store monotonically increases
                     (hash-set! seen c (join-store σ last-σ))
                     ;; Add the updated store with next steps to workset
                     (printf "Stepping ~a~%" c)
                     (define-values (∆ cs*) (stepper (cons σ c)))
                     (set! todo (∪1 todo (cons (update ∆ σ) cs*))))
                   (loop)])))))

(define-syntax-rule (mk-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
  (let-values ([(σ cs) fst])
    (for/fold ([last-σ (hash)]
               [final-cs ∅])
        ([s (fix (wide-step step) (set (cons σ cs)))])
      (match s
        [(cons σ cs)
         (values (join-store last-σ σ)
                 (for/set #:initial final-cs ([c (in-set cs)]
                                              #:when (ans^? c))
                          c))]
        [_ (printf "bad output ~a~%" s)])))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable pre-allocated store / mutable worklist
(define global-σ #f)
(define todo #f)
(define unions 0)
(define seen #f)
(define next-loc #f)
(define contour-table #f)

(define (ensure-σ-size)
  (when (= next-loc (vector-length global-σ))
    (set! global-σ
          (for/vector #:length (* 2 next-loc) #:fill ∅ ;; ∅ → '()
                      ([v (in-vector global-σ)]
                       [i (in-naturals)]
                       #:when (< i next-loc))
                      v))))

(define-syntax-rule (get-contour-index!-0 c)
  (or (hash-ref contour-table c #f)
      (begin0 next-loc
              (ensure-σ-size)
              (hash-set! contour-table c next-loc)
              (set! next-loc (add1 next-loc)))))

(define-for-syntax yield!
  (syntax-parser [(_ e) #'(let ([c e])
                            (unless (= unions (hash-ref seen c -1))
                              (hash-set! seen c unions)
                              (set! todo (∪1 todo c))))])) ;; ∪1 → cons

(define-syntax-rule (make-var-contour-0-prealloc x δ)
  (cond [(exact-nonnegative-integer? x) x]
        [else (get-contour-index!-0 x)]))

(define (prepare-prealloc parser sexp)
  (define nlabels 0)
  (define (fresh-label!) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define (fresh-variable! x) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define e (parser sexp fresh-label! fresh-variable!))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (set! global-σ (make-vector (* 2 nlabels) ∅)) ;; ∅ → '()
  (set! next-loc nlabels)
  (set! contour-table (make-hash))
  (set! unions 0)
  (set! todo ∅)
  (set! seen (make-hash))
  e)

(define (join! a vs)
  (define prev (vector-ref global-σ a))
  (define added? (not (subset? vs prev)))
  (when added?
    (vector-set! global-σ a (∪ vs prev))
    (set! unions (add1 unions))))

(define (join*! as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join! a vs)))

(define-syntax-rule (bind-join! (σ* σ a vs) body)
  (begin (join! a vs) body))
(define-syntax-rule (bind-join*! (σ* σ as vss) body)
  (begin (join*! as vss) body))

(define-syntax-rule (global-getter σ* a)
  (vector-ref global-σ a))

(define-syntax-rule (mk-prealloc^-fixpoint name ans^? ans^-v)
  (define (name step fst)
    (let loop ()
      (cond [(∅? todo) ;; → null?
             (define vs
               (for*/set ([(c at-unions) (in-hash seen)]
                          #:when (ans^? c))
                 (ans^-v c)))
             (cons (restrict-to-reachable/vector global-σ vs)
                   vs)]
            [else
             (define todo-old todo)
             (set! todo ∅)                        ;; → '()
             (for ([c (in-set todo-old)]) (step c)) ;; → in-list
             (loop)]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete semantics

(define (eval-widen b)
  (cond [(atomic? b) b]
        [else (error "Unknown base value" b)]))

(define (lazy-force σ x)
  (match x
    [(addr a) (lookup-sto σ a)]
    [v (set v)]))

(define-syntax-rule (lazy-force! σ x)
  (match x
    [(addr a) (vector-ref global-σ a)]
    [v (set v)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define ε '())
(define (truncate δ k)
  (cond [(zero? k) '()]
        [(empty? δ) '()]
        [else
         (cons (first δ) (truncate (rest δ) (sub1 k)))]))

(define (widen^ b)
  (match b
    [(? number?) 'number]
    [(? string?) 'string]
    [(? symbol?) 'symbol]
    [(? boolean?) b]
    [(or 'number 'string 'symbol) b]
    [else (error "Unknown base value" b)]))

(define-syntax-rule (lazy-delay σ a) (set (addr a)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of common parameterizations

(define-syntax-rule (with-narrow-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (∪1 target-cs e)])])
   body))

(define-syntax-rule (with-σ-passing-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (values target-σ (∪1 target-cs e))])])
   body))

(define-syntax-rule (with-mutable-worklist body)
  (splicing-syntax-parameterize
   ([yield-meaning yield!])
   body))

(define-syntax-rule (with-lazy body)
  (splicing-syntax-parameterize
   ([delay (make-rename-transformer #'lazy-delay)]
    [force (make-rename-transformer #'lazy-force)])
   body))

(define-syntax-rule (with-0-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0)])
   body))

(define-syntax-rule (with-0-ctx/prealloc body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0-prealloc)])
   body))

(define-syntax-rule (with-∞-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-∞)]
    [make-var-contour (make-rename-transformer #'make-var-contour-k)])
   body))

(define-syntax-rule (with-σ-passing body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-whole)]
    [bind-join* (make-rename-transformer #'bind-join*-whole)]
    [getter (make-rename-transformer #'hash-ref)]
    ;; separate out this force?
    [force (make-rename-transformer #'lazy-force)])
   body))

(define-syntax-rule (with-mutable-store body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join!)]
    [bind-join* (make-rename-transformer #'bind-join*!)]
    [getter (make-rename-transformer #'global-getter)]
    ;; separate out this force?
    [force (make-rename-transformer #'lazy-force!)])
   body))

(define-syntax-rule (with-σ-∆s body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-∆s)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s)]
    [getter (make-rename-transformer #'hash-ref)]
    [force (make-rename-transformer #'lazy-force)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators

;; Compiled wide concrete store-passing set monad
#;
(with-lazy
 (with-∞-ctx
  (with-σ-passing
   (with-narrow-set-monad
    (splicing-syntax-parameterize ([widen (make-rename-transformer #'eval-widen)])
      (mk-analysis #:aval lazy-eval/c
                   #:compiled #:set-monad #:σ-passing
                   #:kcfa +inf.0))))))

(mk-set-fixpoint^ fix eval-set-fixpoint^ ans^?)
(with-lazy
 (with-∞-ctx
  (with-σ-passing
   (with-σ-passing-set-monad
    (splicing-syntax-parameterize ([widen (make-rename-transformer #'eval-widen)])
      (mk-analysis #:aval lazy-eval^/c #:ans ans^
                   #:fixpoint eval-set-fixpoint^
                   #:compiled #:set-monad #:wide #:σ-passing
                   #:kcfa +inf.0))))))


(provide lazy-eval^/c)

(mk-set-fixpoint^ fix 0cfa-set-fixpoint^ 0cfa-ans^?)
(with-lazy
 (with-0-ctx
  (with-σ-passing
   (with-σ-passing-set-monad
    (splicing-syntax-parameterize ([widen (make-rename-transformer #'widen^)])
      (mk-analysis #:aval lazy-0cfa^/c
                   #:ans 0cfa-ans^
                   #:fixpoint 0cfa-set-fixpoint^ #:σ-passing
                   #:compiled #:wide #:set-monad))))))

(provide lazy-0cfa^/c)

;; FIXME bind-join conses onto a hash rather than a list
#;#;#;
(mk-∆-fix^ lazy-0cfa∆^-fixpoint 0cfa∆-ans^?)
(with-lazy
 (with-0-ctx
  (with-σ-∆s
   (with-σ-passing-set-monad
    (splicing-syntax-parameterize ([widen (make-rename-transformer #'widen^)])
      (mk-analysis #:aval lazy-0cfa∆/c
                   #:ans 0cfa∆-ans^
                   #:fixpoint lazy-0cfa∆^-fixpoint
                   #:compiled #:wide #:σ-∆s #:set-monad))))))
(provide lazy-0cfa∆/c)

(mk-prealloc^-fixpoint prealloc/imperative-fixpoint prealloc-ans? prealloc-ans-v)
(with-lazy
 (with-0-ctx/prealloc
  (with-mutable-store
   (with-mutable-worklist
    (splicing-syntax-parameterize ([widen (make-rename-transformer #'widen^)])
      (mk-analysis #:aval lazy-0cfa^/c!-prepared
                   #:ans prealloc-ans
                   #:fixpoint prealloc/imperative-fixpoint
                   #:pre-alloc #:compiled #:imperative #:wide))))))
(define (lazy-0cfa^/c! sexp)
  (lazy-0cfa^/c!-prepared (prepare-prealloc parse-prog sexp)))
(provide lazy-0cfa^/c!)

;; concrete compiled strict/lazy
;; 1cfa compiled strict/lazy
;; 0cfa compiled strict/lazy
