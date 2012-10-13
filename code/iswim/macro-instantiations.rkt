#lang racket
(require (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         "env.rkt" "ast.rkt" "progs.rkt"
         "macro-all.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Laziness, kcfa, concrete/abstract

(define-syntax-rule (delay σ a) (list (addr a)))

(define-syntax-rule (make-var-contour-0 x δ) x)
(define-syntax-rule (make-var-contour-k x δ) (cons x δ))

(define (widen^ b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (1cfa-tick δ l) l)
(define ((kcfa-tick K) δ l)
  (let ensure-K ([δ (cons l δ)] [k K])
    (cond [(zero? k) '()] ;; truncate
          [(pair? δ) (cons (car δ) (ensure-K (cdr δ) (sub1 k)))]
          [else δ])))

(define (prepare sexp)
  (define nlabels 0)
  (define (fresh-label!) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define (fresh-variable! x) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (parse sexp fresh-label! fresh-variable!))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Global store, imperative worklist
(begin-for-syntax
 (define global-body #'(λ (inner-σ outer-σ body) body))
 (define global-loop #'(λ (hoist binds outer-σ guards) #`(for* #,guards #,binds))))

(define-for-syntax (yield! s)
  (quasisyntax/loc s
    (let ([c #,s])
      (unless (= unions (hash-ref seen c -1))
        (hash-set! seen c unions)
        (set! todo (cons c todo))))))

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
  (set! σ (make-vector nlabels '()))
  (set! unions 0)
  (set! todo '())
  (set! seen (make-hash))
  e)

(define (prealloc-get-cont σ l) (vector-ref σ l))

(define-syntax-rule (prealloc-bind-join-one (σ* σ a v) body)
  (begin (join-one! a v) body))
(define-syntax-rule (prealloc-bind-join (σ* σ a vs) body)
  (begin (join! a vs) body))
(define-syntax-rule (prealloc-bind-push (σ* a* σ δ l ρ k) body)
  (begin (join-one! l k)
         (let ([a* l]) body)))

;; Store (Addr + Val) -> Set Val
(define-syntax-rule (prealloc-force σ* v)
  (match v
    [(addr loc) (vector-ref σ loc)]
    [_ (list v)]))

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
#;
(define-syntax mk-wide-imperative-analysis
  (mk-mk-analysis global-body global-loop yield!))
#;
(mk-wide-imperative-analysis
 #:bind-join-one prealloc-bind-join-one
 #:bind-join prealloc-bind-join
 #:bind-push prealloc-bind-push
 #:tick values ;; doesn't matter
 #:get-cont prealloc-get-cont
 #:force prealloc-force
 #:delay delay
 #:widen widen^
 #:make-var-contour make-var-contour-0
 #:fixpoint prealloc/imperative-fixpoint
 #:aval aval! ;; constructed evaluator to use/provide
 #:pre-alloc #:compiled #:wide #:imperative)
#;
(let ([prepped (prepare-prealloc church)])
  (time (aval! prepped)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Store deltas, real generators
(begin-for-syntax
 (define non-global/generator-body
   #'(λ (inner-σ outer-σ body) #`(begin #,body #,inner-σ)))
 ;; σ-∆s and σ threading
 (define non-global/generator-loop
   #'(λ (hoist binds outer-σ guards)
      #`(begin (real-yield (for*/fold ([acc-σ '()]) #,guards
                      (let #,hoist (let ([#,outer-σ '()]) #,binds))))
               'done)))
 (define (real-yield-fn s) #`(real-yield #,s)))

;; Apply deltas to the store
(define (update ∆ σ)
  (match ∆
    ['() σ]
    [(cons (cons a xs) ∆) (update ∆ (join σ a xs))]))

(define-syntax mk-generator/σ-∆s-analysis
  (mk-mk-analysis non-global/generator-body
                  non-global/generator-loop
                  real-yield-fn))

(define ((σ-∆s/generator/wide-step-specialized step) state)
  (match state
    [(cons σ cs)
     (define-values (cs* ∆)
       (for/fold ([cs* (set)] [∆* '()])
         ([c cs]
          #:unless (ans? c))
         (define gen (step (cons σ c)))
         (define-values (cs** ∆**)
           (for/fold ([cs** cs*] [last #f])
               ([c (in-producer gen (λ (x) (eq? 'done x)))])
             (cond [(list? c) (values cs** (if last (append c last) c))]
                   [else (values (set-add cs** c) last)])))
         (define ∆*** (if (list? ∆**) (append ∆** ∆*) ∆*))
         (values cs** ∆***)))
     (cons (update ∆ σ) (set-union cs cs*))]))

(define (generator/wide/σ-∆s-fixpoint step fst)
  (define wide-step (σ-∆s/generator/wide-step-specialized step))
  (define cs (if (eq? 'done (generator-state fst)) (error 'WAT) (fst)))
  (define ∆ (if (eq? 'done (generator-state fst)) '() (fst)))
  (define fst-s (cons (update ∆ (hash)) (set cs)))
  (define snd (wide-step fst-s))
  (let loop ((next snd) (prev fst-s))
    (cond [(equal? next prev)
           (for/set ([c (cdr prev)]
                     #:when (ans? c))
             (ans-v c))]
          [else (loop (wide-step next) next)])))

(define-syntax-rule (σ-∆s-bind-join-one (∆* ∆ a v) body)
  (let ([∆* (cons (cons a (set v)) ∆)]) body))
(define-syntax-rule (σ-∆s-bind-join (∆* ∆ a vs) body)
  (let ([∆* (cons (cons a vs) ∆)]) body))
(define-syntax-rule (σ-∆s-bind-push (∆* a* ∆ δ l ρ k) body)
  (let ([∆* (cons (cons l (set k)) ∆)]
        [a* l])
    body))

(define (force σ v)
  (match v
    [(addr a) (lookup-store σ a)]
    [_ (set v)]))

(mk-generator/σ-∆s-analysis
 #:bind-join-one σ-∆s-bind-join-one
 #:bind-join σ-∆s-bind-join
 #:bind-push σ-∆s-bind-push
 #:tick values ;; doesn't matter
 #:get-cont get-cont
 #:force force
 #:delay delay
 #:widen widen^
 #:make-var-contour make-var-contour-0
 #:fixpoint generator/wide/σ-∆s-fixpoint
 #:aval aval-σ-∆s ;; constructed evaluator to use/provide
 #:compiled #:wide #:generators #:σ-∆s)

(let ([prepped (prepare church)])
  (time (aval-σ-∆s prepped)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Set-monad, wide
(begin-for-syntax
 (define non-global/set-body
   #'(λ (inner-σ outer-σ body)
        #`(values #,inner-σ (set-union acc-states #,body))))
 (define non-global/set-loop
   #'(λ (hoist binds outer-σ guards)
        #`(let*-values ([(outer-σ) '()]
                        [(acc-σ acc-states)
                         (for*/fold ([acc-σ outer-σ] [acc-states (set)]) #,guards
                           #,binds)])
            (cons acc-σ acc-states)))))

(define ((wide-step-specialized step) state)
  (match state
    [(cons σ cs)
     (define-values (cs* σ*)
       (for/fold ([cs* (set)] [σ* σ]) ([c cs])
         (match (step (cons σ c))
           [(cons σ** cs**)
            (values (set-union cs* cs**) (join-store σ* σ**))])))
     (cons σ* cs*)]))

(define (set/wide-fixpoint step fst)
  (define wide-step (wide-step-specialized step))
  (let loop ((next (wide-step fst)) (prev fst))
    (if (equal? next prev)
        (for/set ([c (cdr prev)]
                  #:when (ans? c))
          (ans-v c))
        (loop (wide-step next) next))))
