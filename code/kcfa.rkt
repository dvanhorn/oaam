#lang racket
#;
(provide eval eval^ eval/c eval/c^
         lazy-eval lazy-eval^ lazy-eval/c lazy-eval/c^
         0cfa 0cfa^ 0cfa/c 0cfa/c^
         0cfa-step comp-0cfa-step compile-0cfa
         lazy-0cfa lazy-0cfa^ lazy-0cfa/c lazy-0cfa/c^
         1cfa 1cfa^ 1cfa/c 1cfa/c^
         lazy-1cfa lazy-1cfa^ lazy-1cfa/c lazy-1cfa/c^
         widen)
(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt"
         "notation.rkt" "primitives.rkt"
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         racket/stxparam racket/splicing
         (for-syntax syntax/parse racket/syntax))

;; Yield is an overloaded term that will do some manipulation to its
;; input. Yield-meaning is the intended meaning of yield.
(define-syntax-parameter yield-meaning
  (λ (stx) (raise-syntax-error #f "Must parameterize for mk-analysis" stx)))

(define snull (set '()))
(define (toSetOfLists list-of-sets)
  (match list-of-sets
    ['() snull]
    [(cons hdS tail)
     (for*/set ([hd (in-set hdS)]
                [restlist (in-set (toSetOfLists tail))])
       (cons hd restlist))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

;; push  : State -> Sto Addr
;; setter  : ?
;; widen : Val -> Val
;; force : [Rel Sto Val Val]
;; delay : [Rel Sto Addr Val]

(begin-for-syntax
 (define-syntax-rule (implies ante concl) (if ante concl #t)))
;; Expects syntax parameters getter setter widen delay make-var-contour
(define-syntax (mk-analysis stx)
  (syntax-parse stx
    [(_ (~or ;; analysis parameters
         (~once (~seq #:tick tick:id))
         (~optional (~seq #:fixpoint fixpoint:expr)
                    #:defaults ([fixpoint #'fix]))
         (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
         ;; Define the compiler? With what name?
         ;; Analysis strategies flags (requires the right parameters too)
         (~optional (~and #:compiled compiled?))
         (~optional (~and #:pre-alloc pre-alloc?))
         (~optional (~and #:σ-∆s σ-∆s?))
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
     (define global-σ?
       (and (attribute wide?)
            (or (attribute pre-alloc?) (attribute imperative?))))
     (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                    (if (zero? (attribute K))
                        #'(() () ())
                        #'((ρ) (δ) (l)))]
                   [ev: (format-id #'ev "~a:" #'ev)]
                   [ev #'ev]
                   [(σ-op ...) (if global-σ? #'() #'(σ))]
                   [(expander-flags ...)
                    (if (and (attribute wide?) (not global-σ?))
                        #'(#:expander #:with-first-cons)
                        #'())])
       (define-values (pass-yield-to-ev yield-ev)
         (if (attribute compiled?)
             (values #'(...
                        (λ (syn) (syntax-parse syn #:literals (ev)
                                   [(_ (ev args:expr ...))
                                    (syntax/loc syn (ev args ... real-yield))]
                                   [(_ e:expr) (syntax/loc syn (real-yield e))]
                                   [_ (raise-syntax-error #f "One thing" syn)])))
                      #'(...
                         (λ (syn)
                           (syntax-parse syn #:literals (ev)
                             [(_ (ev args:expr ...)) #'(ev args ...)]
                             [(_ e:expr) #'(yield-meaning e)]
                             [_ (raise-syntax-error #f "Pls one" syn)]))))
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
              (λ% (σ ρ k δ yield) (yield (co σ k p)))]))
       
       (define compile-def
         (if (attribute compiled?)
             #`((define-syntax-rule (... (λ% (σ ρ k δ yield) body ...))
                  (syntax-parameterize ([target-σ (and (syntax-parameter-value #'target-σ)
                                                       (make-rename-transformer #'σ))])
                    #,((init-target-cs (syntax? (attribute set-monad?)))
                       (cond [(attribute generators?)
                              #`(λ (σ-op ... ρ-op ... k δ-op ... yield)
                                   (...
                                    (syntax-parameterize ([yield (... #,pass-yield-to-ev)])
                                      body ...)))]
                             [else
                              #`(λ (σ-op ... ρ-op ... k δ-op ...)
                                   (...
                                    (syntax-parameterize ([yield (... #,yield-ev)])
                                      body ...)))]))))
                (define (compile e) #,eval))
             #`((... (define-syntax-rule (λ% (σ ρ k δ yield) body ...)
                       (generator body ...)))
                (define compile values))))

       #`(begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct co (σ k v) (σ-op ... k v) expander-flags ...)
           (struct mt () #:prefab)
           (struct sk! (x k) #:prefab)
           (struct primop (which) #:prefab)
           (mk-op-struct ifk (t e ρ k δ) (t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (x xs es e ρ k δ) (x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (l es vs ρ k δ) (l-op ... es vs ρ-op ... k δ-op ...))
           (mk-op-struct clos (x e ρ) (x e ρ-op ...))
           (splicing-syntax-parameterize ([target-σ #,(or (not global-σ?)
                                                          (syntax? (attribute σ-∆s?)))]
                                          [target-cs #,(syntax? (attribute set-monad?))])
           (define-syntax do-macro
             (mk-do #,(syntax? (attribute σ-∆s?))
                    #,(syntax? (attribute set-monad?))
                    #,global-σ?
                    #,(syntax? (attribute generators?))))
           (splicing-syntax-parameterize ([do (make-rename-transformer #'do-macro)])

           ;; ev is special since it can mean "apply the compiled version" or
           ;; make an actual ev state to later interpret.
           #,@(if (attribute compiled?)
                  #`((define-syntax (ev stx)
                       (syntax-parse stx
                         ;; σ only optional if it's global (wide, imperative/prealloc)
                         [(_ σ e ρ k δ yield) #'(e σ-op ... ρ-op ... k δ-op ... yield)]
                         [(_ σ e ρ k δ) #'(e σ-op ... ρ-op ... k δ-op ...)]
                         [(_ . rest) (raise-syntax-error #f "Bad arg count" stx)]))
                     (define-match-expander ev:
                       (syntax-rules () [(_ σ e ρ k δ) #f])))
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
                 #'#,((init-target-cs (syntax? (attribute set-monad?)))
                      (cond [(attribute generators?)
                             #`(...
                                (syntax-parameterize ([yield (... #,pass-yield-to-ev)])
                                  (real-generator () body ... 'done)))]
                            [else
                             #`(...
                                (syntax-parameterize ([yield (... #,yield-ev)])
                                  (begin (void) body ...)))]))])))

           ;; Let primitives yield single values instead of entire states.
           (define-syntax (with-prim-yield stx)
             (syntax-parse stx
               [(_ k body)
                (define yield-tr (syntax-parameter-value #'yield))
                (define new (λ (syn)
                               (syntax-case syn ()
                                 [(_ v) ;; The only unhygienic thing in the implementation
                                  (yield-tr #'(yield (co target-σ k v)))]
                                 [_ (raise-syntax-error #f "Yield one thing" syn)])))
                #`(syntax-parameterize ([yield #,new])
                    body)]))

           (define (inj e)
             (generator
              (yield
               (ev (hash) ;; store is a hash unless it's preallocated and global, thus dropped
                   (compile e)
                   (hash) ;; no meaning for free variables
                   '()    ;; starting contour is empty
                   (mt)))))

           (define (aval e) (fixpoint step (inj e)))

           #,@compile-def

           (mk-prims prim-meaning)
           ;; [Rel State State]
           (define (step state)
             (match state
               [(co: σ k v)
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
                                  [else (generator)])]
                           [(primop o)
                            (define forced (for/list ([a (in-list (rest args))])
                                             (force σ a)))
                            (with-prim-yield k
                             (do (σ) ([vs (in-set (toSetOfLists forced))])
                               (prim-meaning o σ l δ vs)))]
                           [_ (generator)])))]

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
                         (yield (co σ* k (void)))))])]

               ;; this code is dead when running compiled code.
               [(ev: σ e ρ k δ) #,(if (attribute compiled?)
                                      #'(generator)
                                      eval)]

               [_ (generator)]))))))]))

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
(define-syntax-rule (bind-join-∆s (∆s* ∆s a vs) body)
  (let ([∆s* (cons (cons a vs) ∆s)]) body))
(define-syntax-rule (bind-join*-∆s (∆s* ∆s as vss) body)
  (let ([∆s* (map2-append cons ∆s as vss)]) body))

(define-syntax (the-bind-push stx)
  (syntax-parse stx
    [(_ (σ* a* σ l δ k) body)
     #'(let ([a* (make-var-contour l δ)])
       (bind-join (σ* σ a* (set k)) body))]))

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
;; Concrete semantics

(define (eval-widen b)
  (cond [(atomic? b) b]
        [else (error "Unknown base value" b)]))

(define (lazy-force σ x)
  (match x
    [(addr a) (lookup-sto σ a)]
    [v (set v)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define (truncate δ k)
  (cond [(zero? k) '()]
        [(empty? δ) '()]
        [else
         (cons (first δ)
               (truncate (rest δ) (sub1 k)))]))

(define (widen^ b)
  (match b
    [(? number?) 'number]
    [(? string?) 'string]
    [(? symbol?) 'symbol]
    [(? boolean?) b]
    [(or 'number 'string 'symbol) b]
    [else (error "Unknown base value" b)]))

(define (lazy-delay σ a) (set (addr a)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of common parameterizations

(define-syntax-rule (with-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (λ (stx) (syntax-parse stx [(_ e) #'(∪1 target-cs e)]))])
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

(define-syntax-rule (with-∞-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-∞)]
    [make-var-contour (make-rename-transformer #'make-var-contour-k)])
   body))

(define-syntax-rule (with-σ-passing body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-whole)]
    [bind-join* (make-rename-transformer #'bind-join*-whole)]
    [bind-push (make-rename-transformer #'the-bind-push)]
    [getter (make-rename-transformer #'hash-ref)]
    ;; separate out this force?
    [force (make-rename-transformer #'lazy-force)])
   body))

(define-syntax-rule (with-σ-∆s body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-∆s)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s)]
    [bind-push (make-rename-transformer #'the-bind-push)]
    [getter (make-rename-transformer #'hash-ref)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators

;; Compiled wide concrete store-passing set monad
(with-lazy
 (with-∞-ctx
  (with-σ-passing
   (with-set-monad
    (splicing-syntax-parameterize ([do-body-transformer (λ (stx) stx)
                                    #;
                                    (λ (stx) #`(values target-σ #,stx))]
                                   [widen (make-rename-transformer #'eval-widen)])
      (mk-analysis #:tick tick-∞
                   #:aval eval
                   #:compiled #:set-monad ;#:wide
                   #:kcfa +inf.0))))))
(provide eval)

;; concrete compiled strict/lazy
;; 1cfa compiled strict/lazy
;; 0cfa compiled strict/lazy

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators
#|
(define ((mk-aval step inj) e)
  (for/set ([s (fix step (inj e))]
            #:when (ans? s))
    (match-define (ans σ v) s)
    (ans (restrict-to-reachable σ v) v)))

;; (State -> Setof State) -> Exp -> Set Val
;; 0CFA without store widening

;; (State^ -> Setof State^) -> Exp -> Set Val
;; 0CFA with store widening
(define ((mk-aval^ step inj) e)
  (for/fold ([vs ∅])
    ([s (fix (wide-step step) (inj e))])
    (∪ vs
       (match s
         [(cons cs σ)
          (for/set ([c cs]
                    #:when (ans^? c))
            (ans^-v c))]))))

(define k0 (mt))
(define ε '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ = (cons (Set Conf) Store)

;; (State -> Setof State) -> State^ -> { State^ }
(define ((wide-step step) state)
  (match state
    [(cons cs σ)
     (define ss ((appl step)
                 (for/set ([c cs]) (c->s c σ))))
     (set (cons (for/set ([s ss]) (s->c s))
                (join-stores ss)))]))
|#