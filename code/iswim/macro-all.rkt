#lang racket
(require "ast.rkt"
         "progs.rkt" "fix.rkt"
         (for-syntax syntax/parse racket/syntax)
         (rename-in racket/generator
                    [yield real-yield] ;; I'll take those, thank you.
                    [generator real-generator])
         racket/stxparam)

;; Note that the number of addresses possible is (/ (- 1 (pow nlabels (add1 K))) (- 1 nlabels))

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
      (with-syntax ([((ρ-op ...) (δ-op ...) (l-op ...))
                     (if (zero? (attribute K)) #'(() () ()) #'((ρ) (δ) (l)))]
                    [ev: (format-id #'ev "~a:" #'ev)])
        #`(begin ;; specialize representation given that 0cfa needs less
            (mk-op-struct co (σ k v)
                          #:expander
                          (syntax-parser [(_ σ k v) #,(cond [(attribute wide?)
                                                             #'(cons σ (co-container k v))]
                                                            [else #'(co-container σ k v)])]))
            (mk-op-struct ap (σ fun arg δ l k) (σ-op ... fun arg δ-op ... l-op ... k))
            (mk-op-struct ap-op (σ o vs k) (σ-op ... o vs k))
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
            (mk-op-struct ev (σ e ρ δ k) (e σ-op ... ρ-op ... δ-op ... k)
                          #,@(if (attribute compiled?)
                                 #'(#:expander (syntax-parser [(_ σ e ρ δ k) #'#f]))
                                 #'())) ;; default is what we want if not compiled

            ;; yield colludes with ev to make compiled and
            ;; other strategies look the same
            (...
             (begin
               (define-syntax pass-yield-to-ev ;; real generators
                 (syntax-parser
                   #:literals (ev)
                   [(_ (ev args:expr ...)) (ev args ... real-yield)]
                   [(_ e:expr) (real-yield e)]))
               (define-syntax yield-ev
                 (syntax-parser #:literals (ev)
                                [(_ (ev args:expr ...)) (ev args ...)]
                                [(_ e:expr) #,(yield-meaning #'e)]))))

            (define-syntax-rule (... (λ% (σ ρ k δ yield) body ...))
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
                             (real-generator () body ...))]
                        [else
                         #'(syntax-parameterize ([yield (make-rename-transformer #'yield-ev)])
                             body ...)])])))

            (...
             (define-syntax (do stx)
               (define-syntax-class (join-clause outer-σ new-σ)
                 #:attributes (clause)
                 (pattern [σ*:id #:join-one σ:expr a:expr v:expr]
                          #:with clause
                          (λ (rest)
                             #`(bind-join-one (σ* σ a v) #,(rest #'σ* outer-σ new-σ))))
                 (pattern [σ*:id #:join σ:expr a:expr vs:expr]
                          #:attr clause
                          (λ (rest)
                             #`(bind-join (σ* σ a vs) #,(rest #'σ* outer-σ new-σ))))
                 (pattern [(σ*:id a*:id) #:push σ δ l ρ k]
                          #:attr clause
                          (λ (rest)
                             #`(bind-push (σ* a* σ δ l ρ k) #,(rest #'σ* outer-σ new-σ)))))

               (syntax-parse stx
                 ;; if we don't get our hands on a store, σ is the default.
                 ;; We consider σ* to be an updated store. If using σ or σ* in
                 ;; the value position for a join-clause, then we use the
                 ;; original value of σ. (collude with bind-* macros)
                 [(_ (σ:id σ*:id)
                     ([x:id e:expr] ... (~var joins (join-clauses #'σ #'σ*)) ...) e:expr)
                  ;; flags conflate imperative store and imperative worklist in wide case
                  ;; store-passing/store-δ-accumulation is needed if
                  ;; ¬wide or (¬pre-alloc and ¬imperative)
                  ;; ≡ ¬(wide and (pre-alloc or imperative))
                  (do-loop-meaning
                   (let loop ([j (reverse (attribute joins.clause))]
                              [full do-body-meaning])
                     (cond [(pair? j) (loop (cdr j) (λ _ ((car j) full)))]
                           [else (full #'σ #'σ #'σ*)]))
                   #'σ
                   #'([x e] ...))])))

            #,(if (attribute compiled?)
                  ;; Boucher & Feeley 1996: Compile to closures.
                  ;; Expr -> Comp
                  #'(define (compile e)
                    (match e
                      [(var l x)
                       (λ% (σ ρ k δ yield)
                           (do (σ σ*)
                               ([v (delay (lookup-env ρ x))])
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
                           (do (σ σ*)
                               ([(σ* a) #:push σ δ l ρ k])
                             (yield (ev σ* c0 ρ δ (ar c1 ρ δ l a)))))]
                      [(ife l e0 e1 e2)
                       (define c0 (compile e0))
                       (define c1 (compile e1))
                       (define c2 (compile e2))
                       (λ% (σ ρ k δ)
                           (do (σ σ*)
                               ([(σ* a) #:push σ δ l ρ k])
                             (yield (ev σ* c0 ρ δ (ifk c1 c2 ρ δ a)))))]
                      [(1op l o e)
                       (define c (compile e))
                       (λ% (σ ρ k δ yield)
                           (do (σ σ*)
                               ([(σ* a) #:push σ δ l ρ k])
                             (yield (ev σ* c ρ δ (1opk o δ a)))))]
                      [(2op l o e0 e1)
                       (define c0 (compile e0))
                       (define c1 (compile e1))
                       (λ% (σ ρ k δ yield)
                           (do (σ σ*)
                               ([(σ* a) #:push σ δ l ρ k])
                             (yield (ev σ* c0 ρ δ (2opak o c1 ρ δ a)))))]
                      [_ (error 'compile "Bad ~a" e)]))
                  #'(define compile values))

            ;; "Bytecode" interpreter
            ;;  State -> State^
            (define (step s)
              (match s
                [(co: σ k v)
                 (match k
                   ['mt (generator (do (σ σ*)
                                       ([v (force σ v)])
                                     (yield (ans v))))]
                   [(ar: e ρ δ l a)
                    (generator (yield (ev σ e ρ δ (fn v δ l a))))]
                   [(fn: f δ l a)
                    (generator
                        (do (σ σ*)
                            ([k (get-cont σ a)]
                             [f (force σ f)])
                          (yield (ap σ f v δ l k))))]
                   [(ifk: t e ρ a)
                    (generator
                        (do (σ σ*)
                            ([k (get-cont σ a)]
                             [v (force σ v)])
                          (yield (ev σ (if v t e) ρ δ k))))]

                   [(1opk: o δ a)
                    (generator
                        (do (σ σ*)
                            ([k (get-cont σ a)]
                             [v (force σ v)])
                          (yield (ap-op σ o (list v) k))))]
                   [(2opak: o e ρ δ a)
                    (generator
                        (yield (ev σ e ρ δ (2opfk o v δ a))))]
                   [(2opfk: o u δ a)
                    (generator
                        (do (σ σ*)
                            ([k (get-cont σ a)]
                             [v (force σ v)]
                             [u (force σ u)])
                          (yield (ap-op σ o (list v u) k))))]
                   [_ (error 'step "Bad ~a" k)])]

                [(ap: σ fun v δ k)
                 (match fun
                   [(clos: x e ρ)
                    (define x-addr (make-var-contour x δ))
                    (do (σ σ*)
                        ([σ* #:join σ x-addr (force σ v)])
                      (yield (ev σ* e (extend ρ x x-addr) (tick δ l) k)))]
                   [(rlos: f x e ρ)
                    (define f-addr (make-var-contour f δ))
                    (define x-addr (make-var-contour x δ))
                    (do (σ σ*)
                        ([σ* #:join-one σ f-addr fun]
                         [σ* #:join σ* x-addr (force σ* v)])
                      (yield (ev σ* e (extend (extend ρ x x-addr) f f-addr) (tick δ l) k)))]
                   ;; Anything else is stuck
                   [_ #f])]

                [(ap-op: σ o vs k)
                 (match* (o vs)
                   [('zero? (list (? number? n))) (generator (yield (co σ k (zero? n))))]
                   [('sub1 (list (? number? n)))  (generator (yield (co σ k (widen (sub1 n)))))]
                   [('add1 (list (? number? n)))  (generator (yield (co σ k (widen (add1 n)))))]
                   [('zero? (list 'number))
                    (generator (do (σ σ*)
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

                [(ev: σ e ρ δ k) (error 'TODO "Non-compiled step")]

                [s s]))

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
                       #'(fixpoint step (inj e))]
                      [else ;; must be in set monad
                       #'(fix step (inj e))]))))])))

(begin-for-syntax
 (define (non-global/generator-body inner-σ outer-σ body)
   #`(values #,inner-σ #,body))
 ;; σ-∆s and σ threading
 (define (non-global/generator-loop binds outer-σ guards)
   #`(let ([#,outer-σ '()])
       (real-yield (for*/fold ([acc-σ outer-σ]) #,guards #,binds))
       (real-yield 'done)))

 (define (global-body inner-σ outer-σ body) body)
 (define (global-loop binds outer-σ guards) #`(for* #,guards #,binds))

 (define (non-global/set-body inner-σ outer-σ body)
   #`(values #,inner-σ (set-union acc-states #,body)))
 (define (non-global/set-loop binds outer-σ guards)
   #`(let*-values ([(outer-σ) '()]
                   [(acc-σ acc-states)
                    (for*/fold ([acc-σ outer-σ] [acc-states (set)]) #,guards
                      #,binds)])
       (cons acc-σ acc-states))))

(define-for-syntax (yield! s)
  #`(let ([c s])
      (unless (= unions (hash-ref seen c -1))
        (hash-set! seen c unions)
        (set! todo (cons c todo)))))

(define-syntax mk-wide-imperative-analysis (mk-mk-analysis global-body global-loop yield!))

(define ((wide-step-specialized step) state)
  (match state
    [(cons σ cs)
     (define-values (cs* σ*)
       (for/fold ([cs* (set)] [σ* σ]) ([c cs])
         (match (step (cons σ c))
           [(cons σ** cs**)
            (values (set-union cs* cs**) (join-store σ* σ**))])))
     (cons σ* cs*)]))

(define ((σ-∆s/generator/wide-step-specialized step) state)
  (match state
    [(cons σ cs)
     (define-values (cs* ∆)
       (for/fold ([cs* (set)] [∆* '()])
         ([c cs])
         (define gen (step (cons σ c)))
         (define-values (cs** ∆**)
           (for/fold ([cs** cs*] [last #f])
               ([c (in-producer gen (λ (x) (eq? x 'done)))])
             (cond [last (values (set-add cs** last) c)]
                   [else (values cs** c)])))
         (define-values (cs*** ∆***)
           (cond [(list? ∆**) (values cs** (append ∆** ∆*))]
                 [else (values (set-add cs** ∆**) ∆*)]))
         (values cs*** ∆***)))
     (cons (update ∆ σ) (set-union cs cs*))]))

(define (update ∆ σ)
  (match ∆
    ['() σ]
    [(cons (cons a xs) ∆) (update ∆ (join σ a xs))]))

(define (set/wide-fixpoint step fst)
  (define wide-step (wide-step-specialized step))
  (let loop ((next (wide-step fst)) (prev fst))
    (if (equal? next prev)
        (for/set ([c (cdr prev)]
                  #:when (ans? c))
          (ans-v c))
        (loop (wide-step next) next))))

;; Preparation should do parsing, banging, etc before aval.

;; Store (Addr + Val) -> Set Val
(define (prealloc-force σ v)
  (match v
    [(addr loc) (vector-ref σ loc)]
    [_ (list v)]))

;; Global store, imperative worklist.
(define σ #f)
(define unions 0)
(define todo '())
(define seen #f)

(define (prepare-prealloc sexp)
  (define nlabels 0)
  (define (fresh-label!) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define (fresh-variable! x) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define e (parse sexp fresh-label! fresh-variable!))
  (set! σ (make-vector σ '()))
  (set! unions 0)
  (set! todo '())
  (set! seen (make-hash))
  e)

(define (prealloc-get-cont σ l) (vector-ref σ l))

(define-syntax-rule (prealloc-bind-push (σ* σ δ l ρ k) body)
  (begin (join-one! l k)
         l))

(define (join-one! a v)
  (define prev (vector-ref σ a))
  (unless (member v prev)
    (vector-set! σ a (cons v prev))
    (set! unions (add1 unions))))

(define (join! a vs)
  (define prev (vector-ref σ a))
  (define-values (next added?)
    (for/fold ([res prev] [added? #f])
        ([v (in-list vs)]
         #:unless (member v prev))
      (values (cons v res) #t)))
  (when added?
    (vector-set! σ a next)
    (set! unions (add1 unions))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define (widen b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (prealloc/imperative-fixpoint step fst)
  (let loop ()
    (cond [(null? todo)
           (for*/set ([(c at-unions) (in-hash seen)]
                      #:when (ans? c))
             (ans-v c))]
          [else
           (define todo-old todo)
           (set! todo '())
           (for ([c (in-list todo-old)]) (step c))
           (loop)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ -> State^
;; Specialized from wide-step : State^ -> { State^ } ≈ State^ -> State^
(define ((imperative/wide-step-specialized step) seen)
  (define todo-old todo)
  (set! todo '())
  (for ([c (in-list todo-old)]) (step c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Boilerplate
;; Store Store -> Store

(define (1cfa-tick δ l) l)
(define ((kcfa-tick K) δ l)
  (let ensure-K ([δ (cons l δ)] [k K])
    (cond [(zero? k) '()] ;; truncate
          [(pair? δ) (cons (car δ) (ensure-K (cdr δ) (sub1 k)))]
          [else δ])))
(define-syntax-rule (make-var-contour-k x δ) (cons x δ))
(define-syntax-rule (make-var-contour-0 x δ) x)

(define (join-store σ1 σ2)
  (for/fold ([σ σ1])
    ([k×v (in-hash-pairs σ2)])
    (hash-set σ (car k×v)
              (set-union (cdr k×v)
                         (hash-ref σ (car k×v) (set))))))

;; Set State -> Store
(define (join-stores ss)
  (for/fold ([σ (hash)])
    ([s ss])
    (join-store σ (car s))))

(define (join-one σ a x)
  (hash-set σ a
            (set-add (hash-ref σ a (set)) x)))
(define (join-one* σ as xs)
  (cond [(empty? as) σ]
        [else (join-one* (join-one σ (first as) (first xs))
                         (rest as)
                         (rest xs))]))
(define (join σ a s)
  (hash-set σ a
            (set-union s (hash-ref σ a (set)))))

(define (get-cont σ l)
  (hash-ref σ l (λ () (error 'get-cont "Unbound cont ~a" l))))
(define (extend ρ x v)
  (hash-set ρ x v))

;; Make a struct that looks like it has all the fields given, but really
;; only has the subfields.
(define-syntax mk-op-struct
  (syntax-parser
    [(_ stx name:id (fields:id ...) (subfields:id ...)
        (~optional (~seq #:expander expander:expr) ;; want a different match expander?
                   #:defaults ([expander
                                #'(λ (stx)
                                     (syntax-case stx ()
                                       [(_ fields ...)
                                        #'(container subfields ...)]))])))

     #:fail-unless (for/and ([s (in-list (syntax->list #'(subfields ...)))])
                     (for/or ([f (in-list (syntax->list #'(fields ...)))]) 
                       (free-identifier=? f s)))
     "Subfields should be contained in fields list."
     (with-syntax* ([container (format-id #'name "~a-container" #'name)]
                    [name: (format-id #'name "~a:" #'name)])
       #'(begin (struct container (subfields ...) #:prefab)
                (define-syntax-rule (name fields ...) (container subfields ...))
                (define-match-expander name: expander)))]))

(define-syntax-rule (for/union guards body1 body ...)
  (for/fold ([res (set)]) guards (set-union res (let () body1 body ...))))
(define-syntax-rule (for*/union guards body1 body ...)
  (for*/fold ([res (set)]) guards (set-union res (let () body1 body ...))))

#|
 (σ:id ρ:id δ:id x:id) ;; get the identifiers (x is for lookup-env)
 ;; states
         (~once [#:co co:id]) (~once [#:ev ev:id])
         (~once [#:ap ap:id]) (~once [#:ap-op ap-op:id])
         ;; continuation frames
         (~once [#:fn fn:id]) (~once [#:ar ar:id]) (~once [#:ifk ifk:id])
         (~once [#:1opk 1opk:id])
         (~once [#:2opak 2opak:id]) (~once [#:2opfk 2opfk:id])
         ;; data
         (~once [#:clos clos:id]) (~once [#:rlos rlos:id])
         (~once [#:make-var-contour make-var-contour:id])
         ;; binding forms
         (~once [#:λ% λ%:id])
         (~once [#:lookup-env lookup-env:id])

|#