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
         racket/stxparam
         (for-syntax syntax/parse racket/syntax))

(define-syntax-parameter yield
  (λ (stx)
     (raise-syntax-error #f "Must be within the context of a generator" stx)))
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
(define-syntax (mk-analysis stx)
  (syntax-parse stx
    [(_ (~or ;; analysis parameters
         (~once (~seq #:bind-join-one bind-join-one:id))
         (~once (~seq #:bind-join bind-join:id))
         (~once (~seq #:bind-join* bind-join*:id))
         (~once (~seq #:bind-push bind-push:id))
         (~once (~seq #:tick tick:id))
         (~once (~seq #:getter getter:id))
         (~once (~seq #:force force:id))
         (~once (~seq #:delay delay:id))
         (~once (~seq #:widen widen:id))
         (~once (~seq #:fresh-label! fresh-label!:id))
         (~once (~seq #:fresh-variable! fresh-variable!:id))
         (~once (~seq #:make-var-contour make-var-contour:id))
         (~once (~seq #:fixpoint fixpoint:expr))
         (~once (~seq #:aval aval:id)) ;; name the evaluator to use/provide
         ;; Define the compiler? With what name?
         ;; Analysis strategies flags (requires the right parameters too)
         (~optional (~and #:compiled compiled?))
         (~optional (~and #:pre-alloc pre-alloc?))
         (~optional (~and #:σ-∆s σ-∆s?))
         (~optional (~and #:wide (~bind [(σ-op 1) #'()] [wide? #t]))
                    #:defaults ([(σ-op 1) #'(σ)] [wide? #f]))
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
     "Store deltas and narrow stores are antithetical."
     #:fail-when (and (attribute pre-alloc?) (attribute σ-∆s?))
     "Pre-allocation and store deltas are antithetical."
     #:fail-unless (or (attribute fixpoint) (attribute set-monad?))
     "Cannot use a general fixpoint for step function that doesn't return sets."
     (define global-σ?
       (and (attribute wide?)
            (or (attribute pre-alloc?) (attribute imperative?))))
     (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                    (if (zero? (attribute K)) #'(() () ()) #'((ρ) (δ) (l)))]
                   [ev: (format-id #'ev "~a:" #'ev)]
                   [(σ-gop ...) (if global-σ? #'() #'(σ))]
                   [(expander-flags ...)
                    (if (and (attribute wide?) (not global-σ?))
                        #'(#:expander #:with-first-cons)
                        #'())])
       (define eval ;; what does ev mean?
         #'(match e
             [(var l x)
              (λ% (σ ρ k δ yield)
                  (do ([v (delay σ (lookup-env ρ x))])
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
              (λ% (σ ρ k δ)
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
                  #,(cond [(attribute generators?)
                           #'(λ (σ-op ... ρ-op ... k δ-op ... yield)
                                (...
                                 (syntax-parameterize ([yield (make-rename-transformer #'pass-yield-to-ev)])
                                   body ...)))]
                          [else
                           #'(λ (σ-op ... ρ-op ... k δ-op ...)
                                (...
                                 (syntax-parameterize ([yield (make-rename-transformer #'yield-ev)])
                                   body ...)))]))
                (define (compile e)
                  #,eval))
             #`((... (define-syntax-rule (λ% (σ ρ k δ yield) body ...)
                       (generator body ...)))
                (define compile values))))
       #`(begin ;; specialize representation given that 0cfa needs less
           (mk-op-struct co (σ k v) expander-flags ...)
           (struct mt () #:prefab)
           (struct sk! (x k) (x k) #:prefab)
           (struct primop (which) #:prefab)
           (mk-op-struct ifk (t e ρ k δ) (t e ρ-op ... k δ-op ...))
           (mk-op-struct lrk (x xs es e ρ k δ) (x xs es e ρ-op ... k δ-op ...))
           (mk-op-struct ls (l es vs ρ k δ) (l-op ... es vs ρ-op ... k δ-op ...))
           (mk-op-struct clos (x e ρ) (x e ρ-op ...))
           (define-syntax do (mk-do #,(syntax? (attribute σ-∆s?))
                                    #,(syntax? (attribute set-monad?))
                                    #,global-σ?
                                    #,(syntax? (attribute generators?))))

           ;; ev is special since it can mean "apply the compiled version" or
           ;; make an actual ev state to later interpret.
           #,@(if (attribute compiled?)
                  #`((define-syntax ev
                       (syntax-rules ()
                         ;; σ only optional if it's global (wide, imperative/prealloc)
                         [(_ σ e ρ δ k yield) (e σ-gop ... ρ-op ... δ-op ... k yield)]
                         [(_ σ e ρ δ k) (e σ-gop ... ρ-op ... δ-op ... k)]))
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
                                                      (yield-meaning e))])))))
                  #`((mk-op-struct ev (σ e ρ δ k) (σ-op ... e ρ-op ... δ-op ... k)
                                   expander-flags ...)
                     (define-syntax pass-yield-to-ev (syntax-rules () [(_ e) (yield-meaning e)]))
                     (define-syntax yield-ev (syntax-rules () [(_ e) (yield-meaning e)]))))

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
                [(_ body:expr ...+)
                 (cond [(attribute generators?)
                        #'(syntax-parameterize ([yield (make-rename-transformer #'pass-yield-to-ev)])
                            (real-generator () body ... 'done))]
                       [else
                        #'(syntax-parameterize ([yield (make-rename-transformer #'yield-ev)])
                            (begin (void) body ...))])])))

           #,@compile-def

           (mk-prim-meaning-table getter setter widen delay prim-meaning-table)
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
                                   (do ([(ρ* σ* δ*) #:bind ρ σ l δ xs (rest args)])
                                       (yield (ev σ* e ρ* k δ*)))]
                                  [else (generator)])]
                           [(primop o)
                            (define forced (for/list ([a (in-list (rest args))])
                                             (force σ a)))
                            (define meaning (hash-ref prim-meaning-table o))
                            (cond [(changes-store? o)
                                   (do (σ) ([vs (in-set (toSetOfLists forced))]
                                            #:when (check-good o vs)
                                            ;; FIXME
                                            [(σ* rs) #:prim (apply meaning σ l δ vs)]
                                            [r (in-list rs)])
                                     (yield (co σ* k r)))]
                                  [(reads-store? o)
                                   (do (σ) ([vs (in-set (toSetOfLists forced))]
                                            #:when (check-good o vs)
                                            [r (in-list (apply meaning σ vs))])
                                     (yield (co σ k r)))]
                                  [else
                                   (do (σ) ([vs (in-set (toSetOfLists forced))]
                                            #:when (check-good o vs)
                                            [r (in-list (apply meaning vs))])
                                     (yield (co σ k r)))])]
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
                       (do (σ) ([σ* #:set σ l v]
                                [k (getter σ a)])
                         (yield (co σ* k (void)))))])]

               ;; this code is dead when running compiled code.
               [(ev: σ e ρ k δ) #,(if (attribute compiled?)
                                      #'(generator)
                                      eval)]

               [_ (generator)]))

           (define (inj e)
             (generator
                 (yield
                  (ev (hash) ;; store is a hash unless it's preallocated and global, thus dropped
                      (compile e)
                      (hash) ;; no meaning for free variables
                      '()    ;; starting contour is empty
                      (mt)))))

           (define (aval e)
             #,(cond [(attribute fixpoint)
                      #'(fixpoint step (inj e))]
                     [else ;; must be in set monad
                      #'(fix step (inj e))]))))]))
#|
(define ((push K) σ l δ k)
  (define a (cons l δ))
  (values (join σ a (set k))
          a))

(define ((bind K) ρ σ l δ xs vs)
  (define δ* (truncate (cons l δ) K))
  (define as (map (λ (x) (cons x δ*)) xs))
  (define ρ* (extend* ρ xs as))
  (define σ* (join* σ as (map (λ (v) (force σ v)) vs)))
  (values ρ* σ* δ*))

(define (ev-interp  σ e ρ k δ) (set (ev σ e ρ k δ)))
(define (ev-compile σ c ρ k δ) (c σ ρ k δ))

(define mk-step  (mk-mk-step ev-interp))

(define (mk-comp-step push bind getter setter widen force delay)
  (values (mk-step push bind getter setter widen force delay)
          (mk-comp push delay)
          ((mk-mk-step ev-compile) push bind getter setter widen force delay)))

(define (mk-comp push delay)
  ;; Expr -> (Store Env Cont Contour -> State)
  (define (compile e)
    (match e
      [(var l x)
       (λ (σ ρ k δ)
         (for/set ((v (delay σ (lookup-env ρ x))))
                  (co σ k v)))]
      [(datum l d) (λ (σ ρ k δ) (set (co σ k d)))]
      [(primr l which)
       (define p (primop which))
       (λ (σ ρ k δ) (set (co σ k p)))]
      [(lam l x e)
       (define c (compile e))
       (λ (σ ρ k δ) (set (co σ k (clos x c ρ))))]
    [(lrc l xs es b)
     (define c (compile (first es)))
     (define cs (map compile (rest es)))
     (define cb (compile b))
     (define x (first xs))
     (define xs* (rest xs))
     (define ss (map (λ _ ∅) xs))
     (λ (σ ρ k δ)
       (define-values (σ0 a) (push σ l δ k))
       (define as (map (λ (x) (cons x δ)) xs))
       (define ρ* (extend* ρ xs as))
       (define σ* (join* σ0 as (map (λ _ ∅) xs)))
       (c σ* ρ* (lrk x xs* cs cb ρ* a δ) δ))]
    [(app l e es)
     (define c (compile e))
     (define cs (map compile es))
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c σ* ρ (ls l cs '() ρ a δ) δ))]
    [(ife l e0 e1 e2)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (define c2 (compile e2))
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c0 σ* ρ (ifk c1 c2 ρ a δ) δ))]
    [(st! l x e)
     (define c (compile e))
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c σ* ρ (sk! (lookup-env ρ x) a) δ))]
    [(primr l which) (define p (primop which))
     (λ (σ ρ k δ) (set (co σ k p)))]))
  compile)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete semantics

(define (eval-widen b)
  (cond [(atomic? b) b]
        [else (error "Unknown base value" b)]))

(define (hash-getter σ addr)
  (hash-ref σ addr (λ () (error 'getter "Unbound addr ~a" addr))))
(define (mk-eval-setter force)
  (λ (σ l v) (extend σ l (force σ v))))

(define (mk-kcfa-setter force)
  (λ (σ l v) (join σ l (force σ v))))

(define (force σ x)
  (match x
    [(addr a) (lookup-sto σ a)]
    [v (set v)]))

(define strict-eval-setter
  (mk-eval-setter (λ (_ v) (set v))))

(define lazy-eval-setter
  (mk-eval-setter force))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define (truncate δ k)
  (cond [(zero? k) '()]
        [(empty? δ) '()]
        [else
         (cons (first δ)
               (truncate (rest δ) (sub1 k)))]))

(define (widen b)
  (match b
    [(? number?) 'number]
    [(? string?) 'string]
    [(? symbol?) 'symbol]
    [(? boolean?) b]
    [(or 'number 'string 'symbol) b]
    [else (error "Unknown base value" b)]))

(define (delay σ x) (set (addr x)))

(define strict-kcfa-setter 
  (mk-kcfa-setter (λ (_ v) (set v))))

(define lazy-kcfa-setter
  (mk-kcfa-setter force))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of transition relations

(define-values (eval-step compile-eval comp-eval-step)
  (mk-comp-step (push +inf.0)
                (bind +inf.0)
                hash-getter
                strict-eval-setter
                eval-widen
                (lambda (σ x) (set x))
                lookup-sto))

(define-values (lazy-eval-step compile-lazy-eval comp-lazy-eval-step)
  (mk-comp-step (push +inf.0)
                (bind +inf.0)
                hash-getter
                strict-eval-setter
                eval-widen
                force
                delay))

(define-values (1cfa-step compile-1cfa comp-1cfa-step)
  (mk-comp-step (push 1)
                (bind 1)
                hash-getter
                strict-kcfa-setter
                widen
                (lambda (σ x) (set x))
                lookup-sto))

(define-values (lazy-1cfa-step compile-lazy-1cfa comp-lazy-1cfa-step)
  (mk-comp-step (push 1)
                (bind 1)
                hash-getter
                lazy-kcfa-setter
                widen
                force
                delay))

(define-values (0cfa-step compile-0cfa comp-0cfa-step)
  (mk-comp-step (push 0)
                (bind 0)
                hash-getter
                strict-kcfa-setter
                widen
                (lambda (σ x) (set x))
                lookup-sto))

(define-values (lazy-0cfa-step compile-lazy-0cfa comp-lazy-0cfa-step)
  (mk-comp-step (push 0)
                (bind 0)
                hash-getter
                lazy-kcfa-setter
                widen
                force
                delay))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators

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

;; Exp -> Set State
(define (inj e)
  (set (ev (hash) e (hash) k0 ε)))

;; Exp -> Set State^
(define (inj-wide e)
  (set (cons (set (ev^ e (hash) k0 ε)) (hash))))

(define ((inj/c c) e)
  ((c e) (hash) (hash) k0 ε))

(define ((inj-wide/c c) e)
  (for/set ((s (in-set ((c e) (hash) (hash) k0 ε))))
           (cons (set (s->c s)) (state-σ s))))

(define (mk-evals step comp-step compile)
  (values (mk-aval  step inj)
          (mk-aval^ step inj-wide)
          (mk-aval  comp-step (inj/c compile))
          (mk-aval^ comp-step (inj-wide/c compile))))

(define-values (eval eval^ eval/c eval/c^)
  (mk-evals eval-step comp-eval-step compile-eval))

(define-values (lazy-eval lazy-eval^ lazy-eval/c lazy-eval/c^)
  (mk-evals lazy-eval-step comp-lazy-eval-step compile-lazy-eval))

(define-values (0cfa 0cfa^ 0cfa/c 0cfa/c^)
  (mk-evals 0cfa-step comp-0cfa-step compile-0cfa))

(define-values (lazy-0cfa lazy-0cfa^ lazy-0cfa/c lazy-0cfa/c^)
  (mk-evals lazy-0cfa-step comp-lazy-0cfa-step compile-lazy-0cfa))

(define-values (1cfa 1cfa^ 1cfa/c 1cfa/c^)
  (mk-evals 1cfa-step comp-1cfa-step compile-1cfa))

(define-values (lazy-1cfa lazy-1cfa^ lazy-1cfa/c lazy-1cfa/c^)
  (mk-evals lazy-1cfa-step comp-lazy-1cfa-step compile-lazy-1cfa))


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