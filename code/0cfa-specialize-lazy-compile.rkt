#lang racket
(provide aval^)
(require "ast.rkt" "data.rkt")

;; 0CFA in the AAM style on some hairy Church numeral churning

;; + compilation phase
;; + lazy non-determinism
;; + specialized step & iterator

;; State  = (cons Conf Store)
;; State^ = (cons (Set Conf) Store)

;; Comp = Store Env Cont -> State^


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Compiled" Machine

;; Compile away interpretive overhead of "ev" states

;; Expr -> Comp
(define (compile e)
  (match e
    [(var l x)
     (λ (σ ρ k)
       (cons σ (set (co^ k (addr (lookup-env ρ x))))))]
    [(num l n)   (λ (σ ρ k) (cons σ (set (co^ k n))))]
    [(bln l b)   (λ (σ ρ k) (cons σ (set (co^ k b))))]
    [(lam l x e)
     (define c (compile e))
     (λ (σ ρ k) (cons σ (set (co^ k (clos l x c ρ)))))]
    [(rec f (lam l x e))
     (define c (compile e))
     (λ (σ ρ k) (cons σ (set (co^ k (rlos l f x c ρ)))))]
    [(app l e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (σ ρ k)
       (define-values (σ* a) (push σ l ρ k))
       (c0 σ* ρ (ar c1 ρ a)))]
    [(ife l e0 e1 e2)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (define c2 (compile e2))
     (λ (σ ρ k)
       (define-values (σ* a) (push σ l ρ k))
       (c0 σ* ρ (ifk c1 c2 ρ a)))]
    [(1op l o e)
     (define c (compile e))
     (λ (σ ρ k)
       (define-values (σ* a) (push σ l ρ k))
       (c σ* ρ (1opk o a)))]
    [(2op l o e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (σ ρ k)
       (define-values (σ* a) (push σ l ρ k))
       (c0 σ* ρ (2opak o c1 ρ a)))]))

(struct addr (a) #:transparent)
;; Store (Addr + Val) -> Set Val
(define (get-val σ v)
  (match v
    [(addr loc) (hash-ref σ loc (λ () (error "~a ~a" loc σ)))]
    [_ (set v)]))

;; "Bytecode" interpreter
;;  State -> State^
(define (step-compiled^ s)
  (match s
    [(cons σ (co^ k v))
     (match k
       ['mt (cons σ (for*/set ((v (get-val σ v)))
                              (ans^ v)))]
       [(ar c ρ l) (c σ ρ (fn v l))]
       [(fn f l)
        (cons σ
              (for*/set ([k (get-cont σ l)]
                         [f (get-val σ f)])
                        (ap^ f v k)))]
       [(ifk c a ρ l)
        (define states^
          (for*/set ([k (get-cont σ l)]
                     [v (get-val σ v)])
                    ((if v c a) σ ρ k)))

        (define-values (σ* cs*)
          (for/fold ([σ σ] [cs (set)])
            ([s states^])
            (match s
              [(cons σ* cs*)
               (values (join-store σ* σ)
                       (set-union cs* cs))])))
        (cons σ* cs*)]

       [(1opk o l)
        (cons σ
              (for*/set ([k (get-cont σ l)]
                         [v (get-val σ v)])
                        (ap-op^ o (list v) k)))]
       [(2opak o c ρ l)
        (c σ ρ (2opfk o v l))]
       [(2opfk o u l)
        (cons σ
              (for*/set ([k (get-cont σ l)]
                         [v (get-val σ v)]
                         [u (get-val σ u)])
                        (ap-op^ o (list v u) k)))])]

    [(cons σ (ap^ fun a k))
     (match fun
       [(clos l x c ρ)
        (define-values (ρ* σ*) (bind s))
        (c σ* ρ* k)]
       [(rlos l f x c ρ)
        (define-values (ρ* σ*) (bind s))
        (c σ* ρ* k)]
       ;; Anything else is stuck
       [_ (cons σ (set))])]

    [(cons σ (ap-op^ o vs k))
     (match* (o vs)
       [('zero? (list (? number? n))) (cons σ (set (co^ k (zero? n))))]
       [('sub1 (list (? number? n)))  (cons σ (set (co^ k (widen (sub1 n)))))]
       [('add1 (list (? number? n)))  (cons σ (set (co^ k (widen (add1 n)))))]
       [('zero? (list 'number))
        (cons σ (set (co^ k #t)
                     (co^ k #f)))]
       [('sub1 (list 'number)) (cons σ (set (co^ k 'number)))]
       [('* (list (? number? n) (? number? m)))
        (cons σ (set (co^ k (widen (* m n)))))]
       [('* (list (? number? n) 'number))
        (cons σ (set (co^ k 'number)))]
       [('* (list 'number 'number))
        (cons σ (set (co^ k 'number)))]
       ;; Anything else is stuck
       [(_ _) (cons σ (set))])]

    [(cons σ c)
     (cons σ (set))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete semantics
#;#;#;
(define (widen b)
  (cond [(number? b) b]
        [else (error "Unknown base value" b)]))

(define (bind s)
  (match s
    [(ap σ (clos l x e ρ) v k)
     (define a
       (add1 (for/fold ([i 0])
               ([k (in-hash-keys σ)])
               (max i k))))
     (values (extend ρ x a)
             (join σ a (set v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (define a
       (add1 (for/fold ([i 0])
               ([k (in-hash-keys σ)])
               (max i k))))
     (define b (add1 a))
     (values (extend (extend ρ x a) f b)
             (join (join σ a (set v)) b (set (rlos l f x e ρ))))]))

(define (push σ l ρ k)
  (define a
    (add1 (for/fold ([i 0])
            ([k (in-hash-keys σ)])
            (max i k))))
  (values (join σ a (set k))
          a))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics
(define (widen b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (bind s)
  (match s
    [(cons σ (ap^ (clos l x e ρ) v k))
     (values (extend ρ x x)
             (join σ x (get-val σ v)))]
    [(cons σ (ap^ (rlos l f x e ρ) v k))
     (values (extend (extend ρ x x) f f)
             (join-one (join σ x (get-val σ v)) f (rlos l f x e ρ)))]))

(define (push σ l ρ k)
  (values (join-one σ l k)
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
    (if (equal? next prev)
        (for/set ([c (cdr prev)]
                  #:when (ans^? c))
                 (ans^-v c))
        (loop (wide-step-specialized next) next))))

;; Exp -> Set State
(define (inj e)
  ((compile e) (hash) (hash) 'mt))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; Store Store -> Store
(define (join-store σ1 σ2)
  (for/fold ([σ σ1])
    ([k×v (in-hash-pairs σ2)])
    (hash-set σ (car k×v)
              (set-union (cdr k×v)
                         (hash-ref σ (car k×v) (set))))))

;; State^ -> State^
;; Specialized from wide-step : State^ -> { State^ } ≈ State^ -> State^
(define (wide-step-specialized state)
  (match state
    [(cons σ cs)
     (define-values (cs* σ*)
       (for/fold ([cs* (set)] [σ* σ])
         ([c cs])
         (match (step-compiled^ (cons σ c))
           [(cons σ** cs**)
            (values (set-union cs* cs**) (join-store σ* σ**))])))
     (cons σ* (set-union cs cs*))]))


