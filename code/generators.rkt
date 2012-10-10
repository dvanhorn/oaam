#lang racket
(provide aval^ widen)
(require "old-ast.rkt" "old-data.rkt"
         "old-progs.rkt"
         racket/generator
         (for-syntax syntax/parse)
         racket/stxparam)

;; 0CFA in the AAM style on some hairy Church numeral churning

;; + compilation phase
;; + lazy non-determinism
;; + specialized step & iterator

;; State  = (cons Conf Store)
;; State^ = (cons (Set Conf) Store)

;; Comp = Store Env Cont -> (values State StoreΔ)

;; We use generators that produce many steps as
(define-syntax-rule (generator^ formals body1 body ...)
  (infinite-generator
   (yield (generator formals body1 body ... (yield 'done)))))

(define <- (case-lambda))
(begin-for-syntax
 (define-syntax-class ids
   #:attributes ((is 1))
   (pattern (~or (~and i:id (~bind [(is 1) (list #'i)]))
                 (is:id ...))))
 (define-syntax-class guards
   #:attributes ((guard-forms 1) (gv 2) (gfrome 1)) #:literals (<-)
   (pattern ((~and (~seq [is:ids e:expr] ...)
                   (~seq start:expr ...))
             (~optional (~seq [v:ids <- frome:expr] ...)
                        #:defaults ([(v 1) #'()]
                                    [(frome 1) #'()])))
            #:with (guard-forms ...) #'(start ...)
            #:with ((gv ...) ...) #'((v.is ...) ...)
            #:with (gfrome ...) #'(frome ...)
            )))
(define-syntax (for/get-vals stx)
  (syntax-parse stx
    [(_ form:id targets:expr gs:guards body1:expr body:expr ...)
     (syntax/loc stx
                 (form targets (gs.guard-forms ...)
                       (let*-values ([(gs.gv ...) gs.gfrome] ...)
                         body1 body ...)))]))
(define-syntax-rule (for*/append guards body1 body ...)
  (for/get-vals for*/fold ([res '()]) guards (append (let () body1 body ...) res)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Compiled" Machine

;; Compile away interpretive overhead of "ev" states

;; Expr -> Comp
(define (compile e)
  (match e
    [(var l x)
     (λ (∆ ρ k)
        (values (co^ k (addr (lookup-env ρ x))) ∆))]
    [(num l n)   (λ (∆ ρ k) (values (co^ k n) ∆))]
    [(bln l b)   (λ (∆ ρ k) (values (co^ k b) ∆))]
    [(lam l x e)
     (define c (compile e))
     (λ (∆ ρ k) (values (co^ k (clos l x c ρ)) ∆))]
    [(rec f (lam l x e))
     (define c (compile e))
     (λ (∆ ρ k) (values (co^ k (rlos l f x c ρ)) ∆))]
    [(app l e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (∆ ρ k)
       (define-values (∆* a) (push∆ ∆ l ρ k))
       (c0 ∆* ρ (ar c1 ρ a)))]
    [(ife l e0 e1 e2)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (define c2 (compile e2))
     (λ (∆ ρ k)
        (define-values (∆* a) (push∆ ∆ l ρ k))
        (c0 ∆* ρ (ifk c1 c2 ρ a)))]
    [(1op l o e)
     (define c (compile e))
     (λ (∆ ρ k)
       (define-values (∆* a) (push∆ ∆ l ρ k))
       (c ∆* ρ (1opk o a)))]
    [(2op l o e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (∆ ρ k)
       (define-values (∆* a) (push∆ ∆ l ρ k))
       (c0 ∆* ρ (2opak o c1 ρ a)))]))

;; Store (Addr + Val) -> Set Val
(define (get-val σ v)
  (match v
    [(addr loc) (hash-ref σ loc (λ () (error "~a ~a" loc σ)))]
    [_ (set v)]))

(define-syntax-rule (do/noyield guards body1 body ...)
  (for*/append guards
               (define v (let () body1 body ...))
               (cond [(list? v) v]
                     [else '()])))
(define-syntax-rule (do guards body1 body ...)
  (yield (do/noyield guards body1 body ...)))

(define-syntax-rule (memo-lambda (id) body1 body ...)
  (let ([h (make-hash)])
    (λ (id)
       (match (hash-ref h id #f) ;; XXX: not robust to returning #f
         [#f
          (define v (let () body1 body ...))
          (hash-set! h id v)
          v]
         [v v]))))

;; "Bytecode" interpreter
;;  State -> State^
(define step-compiled^
  (memo-lambda (s)

    (define (ap-op^ o vs k yield)
      (match* (o vs)
        [('zero? (list (? number? n))) (yield (co^ k (zero? n)))]
        [('sub1 (list (? number? n)))  (yield (co^ k (widen (sub1 n))))]
        [('add1 (list (? number? n)))  (yield (co^ k (widen (add1 n))))]
        [('zero? (list 'number))
         (yield (co^ k #t))
         (yield (co^ k #f))]
        [('sub1 (list 'number))
         (yield (co^ k 'number))]
        [('* (list (? number? n) (? number? m)))
         (yield (co^ k (widen (* m n))))]
        [('* (list (? number? n) 'number))
         (yield (co^ k 'number))]
        [('* (list 'number 'number))
         (yield (co^ k 'number))]
        ;; Anything else is stuck
        [(_ _) '()]))

    (define (ap^ σ fun a k yield)
      (match fun
        [(or (? clos?) (? rlos?))
         (do/noyield ([(v ∆) <- (bind σ fun a k)])
           (yield v)
           ∆)]
        ;; Anything else is stuck
        [_ '()]))

    (match s
      [(co^ k v)
       (match k
         ['mt
          (generator^ (σ)
            (do ([v (get-val σ v)])
                (yield (ans^ v))))]
         [(ar c ρ l)
          (define-values (v* ∆) (c '() ρ (fn v l)))
          (generator^ (σ)
            (yield v*)
            (yield ∆))]
         [(fn f l)
          (generator^ (σ)
            (do ([k (get-cont σ l)]
                 [f (get-val σ f)])
              (ap^ σ f v k yield)))]
         [(ifk c a ρ l)
          (generator^ (σ)
            (do ([k (get-cont σ l)]
                 [v (get-val σ v)]
                 [(c* ∆) <- ((if v c a) '() ρ k)])
              (yield c*)
              ∆))]

         [(1opk o l)
          (generator^ (σ)
            (do ([k (get-cont σ l)]
                 [v (get-val σ v)])
              (ap-op^ o (list v) k yield)))]
         [(2opak o c ρ l)
          (define-values (v* ∆) (c '() ρ (2opfk o v l)))
          (generator^ (σ)
            (yield v*)
            (yield ∆))]
         [(2opfk o u l)
          (generator^ (σ)
            (do ([k (get-cont σ l)]
                 [v (get-val σ v)]
                 [u (get-val σ u)])
                (ap-op^ o (list v u) k yield)))])]

      [_ (generator^ (σ) s)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics
(define (widen b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (bind σ fun v k)
  (match fun
    [(clos l x c ρ)
     (c (list (cons x (get-val σ v)))
        (extend ρ x x) k)]
    [(rlos l f x c ρ)
     (c (list (cons f (set (rlos l f x c ρ)))
              (cons x (get-val σ v)))
        (extend (extend ρ x x) f f)
        k)]))

(define (push∆ ∆ l ρ k)
  (values (cons (cons l (set k)) ∆)
          l))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exp -> Set Val
;; 0CFA with store widening and specialized iteration
(define (aval^ e)
  (define fst (inj e))
  (define snd (wide-step-specialized fst))
  ;; wide-step-specialized is monotonic so we only need to check the current
  ;; state against it's predecessor to see if we have reached a fixpoint.
  (let loop ((next snd) (prev fst))
    (cond [(equal? next prev)
           (for/set ([c (cdr prev)]
                     #:when (ans^? c))
             (ans^-v c))]
          [else (loop (wide-step-specialized next) next)])))

;; Exp -> Set State
(define (inj e)
  (define-values (cs ∆) ((compile e) '() (hash) 'mt))
  (cons (update ∆ (hash)) (set cs)))

(define (update ∆ σ)
  (match ∆
    ['() σ]
    [(cons (cons a xs) ∆)
     (update ∆ (join σ a xs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ -> State^
;; Specialized from wide-step : State^ -> { State^ } ≈ State^ -> State^
(define (wide-step-specialized state)
  (match state
    [(cons σ cs)
     (define-values (cs* ∆)
       (for/fold ([cs* (set)] [∆* '()])
         ([c cs])
         (define step (step-compiled^ c))
         (define stepper (step))
         (define-values (cs** ∆**)
           (for/fold ([cs** cs*] [last #f])
               ([c (in-producer stepper (λ (x) (eq? x 'done)) σ)])
             (cond [last (values (set-add cs** last) c)]
                   [else (values cs** c)])))
         (define-values (cs*** ∆***)
           (cond [(list? ∆**) (values cs** (append ∆** ∆*))]
                 [else (values (set-add cs** ∆**) ∆*)]))
         (values cs*** ∆***)))
     (cons (update ∆ σ) (set-union cs cs*))]))

(time (aval^ (parse church values)))
