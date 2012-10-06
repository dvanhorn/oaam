#lang racket
(provide aval^)
(require "ast.rkt"
	 "fixed.rkt")

;; 0CFA in the AAM style, but with a compilation phase, on
;; some hairy Church numeral churning

;; Moral: a simple compilation strategy can eliminate a lot 
;; of analysis-time interpretive overhead.

;; A Val is one of:
;; - Number
;; - Boolean
;; - (clos Lab Sym Exp Env)
;; - (rlos Lab Sym Sym Exp Env)
(struct clos (l x e ρ)   #:transparent)
(struct rlos (l f x e ρ) #:transparent)

;; A Cont is one of:
;; - 'mt
;; - (ar Exp Env Cont)
;; - (fn Val Cont)
;; - (ifk Exp Exp Env Cont)
;; - (1opk Opr Cont)
;; - (2opak Opr Exp Env Cont)
;; - (2opfk Opr Val Cont)
(struct ar (e ρ k)      #:transparent)
(struct fn (v k)        #:transparent)
(struct ifk (c a ρ k)   #:transparent)
(struct 1opk (o k)      #:transparent)
(struct 2opak (o e ρ k) #:transparent)
(struct 2opfk (o v k)   #:transparent)

;; State
(struct state (σ)            #:transparent)
(struct ev state (e ρ k)     #:transparent)
(struct co state (k v)       #:transparent)
(struct ap state (f a k)     #:transparent)
(struct ap-op state (o vs k) #:transparent)
(struct ans state (v)        #:transparent)

(define (lookup ρ σ x)
  (hash-ref σ (hash-ref ρ x)))
(define (lookup-env ρ x)
  (hash-ref ρ x))
(define (get-cont σ l)
  (hash-ref σ l))
(define (extend ρ x v)
  (hash-set ρ x v))
(define (join σ a s)
  (hash-set σ a
            (set-union s (hash-ref σ a (set)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Compiled" Machine

;; Compile away interpretive overhead of "ev" states

;; Expr -> (Store Env Cont -> State)
(define (compile e)
  (match e
    [(var l x)     
     (λ (σ ρ k)
       (set (co σ k (addr (lookup-env ρ x)))))]
    [(num l n)   (λ (σ ρ k) (set (co σ k n)))]
    [(bln l b)   (λ (σ ρ k) (set (co σ k b)))]
    [(lam l x e) 
     (define c (compile e))
     (λ (σ ρ k) (set (co σ k (clos l x c ρ))))]
    [(rec f (lam l x e))
     (define c (compile e))
     (λ (σ ρ k) (set (co σ k (rlos l f x c ρ))))]
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
;; State -> State
(define (step-compiled s)
  (match s
    [(co σ k v)
     (match k
       ['mt (for*/set ((v (get-val σ v)))
              (ans σ v))]
       [(ar c ρ l) (c σ ρ (fn v l))]
       [(fn f l)
        (for*/set ([k (get-cont σ l)]
             [f (get-val σ f)])        
          (ap σ f v k))]
       [(ifk c a ρ l)        
        (for/fold ([s (set)])
          ([k (get-cont σ l)]
           [v (get-val σ v)])
          (set-union s ((if v c a) σ ρ k)))]     
       [(1opk o l)
        (for*/set ([k (get-cont σ l)]
             [v (get-val σ v)])
          (ap-op σ o (list v) k))]
       [(2opak o c ρ l)
        (c σ ρ (2opfk o v l))]
       [(2opfk o u l)
        (for*/set ([k (get-cont σ l)]
             [v (get-val σ v)]
             [u (get-val σ u)])
          (ap-op σ o (list v u) k))])]
       
    [(ap σ fun a k)
     (match fun
       [(clos l x c ρ)
        (define-values (ρ* σ*) (bind s))
        (c σ* ρ* k)]
       [(rlos l f x c ρ)
        (define-values (ρ* σ*) (bind s))
        (c σ* ρ* k)]
       [_ (set s)])]

    [(ap-op σ o vs k)
     (match* (o vs)
       [('zero? (list (? number? n))) (set (co σ k (zero? n)))]
       [('sub1 (list (? number? n)))  (set (co σ k (widen (sub1 n))))]
       [('add1 (list (? number? n)))  (set (co σ k (widen (add1 n))))]
       [('zero? (list 'number))
        (set (co σ k #t)
             (co σ k #f))]
       [('sub1 (list 'number)) (set (co σ k 'number))]
       [('* (list (? number? n) (? number? m)))
        (set (co σ k (widen (* m n))))]
       [('* (list (? number? n) 'number))
        (set (co σ k 'number))]
       [('* (list 'number 'number))
        (set (co σ k 'number))]
       [(_ _) (set s)])]
    
    [_ (set s)]))


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
    [(ap σ (clos l x e ρ) v k)
     (values (extend ρ x x)
             (join σ x (get-val σ v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (values (extend (extend ρ x x) f f)
             (join (join σ x (get-val σ v)) f (set (rlos l f x e ρ))))]))

(define (push σ l ρ k)  
  (values (join σ l (set k))
          l))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exp -> Set Val
;; 0CFA without store widening
(define (aval e)
  (for/set ([s (fix step-compiled (inj e))]
            #:when (ans? s))
           (ans-v s)))

;; Exp -> Set Val
;; 0CFA with store widening
(define (aval^ e)
  (for/fold ([vs (set)])
    ([s (fix wide-step (inj-wide e))])
    (set-union vs
               (match s
                 [(cons cs σ)
                  (for/set ([c cs]
                            #:when (ans^? c))
                           (ans^-v c))]))))

;; Exp -> Set State
(define (inj e)
  ((compile e) (hash) (hash) 'mt))

;; Exp -> Set State^
(define (inj-wide e)
  (for/first ([s (inj e)])
    (set (cons (set (s->c s)) (state-σ s)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ = (cons (Set Conf) Store)

;; Conf
(struct ev^ (e ρ k)     #:transparent)
(struct co^ (k v)       #:transparent)
(struct ap^ (f a k)     #:transparent)
(struct ap-op^ (o vs k) #:transparent)
(struct ans^ (v)        #:transparent)

;; Conf Store -> State
(define (c->s c σ)
  (match c
    [(ev^ e ρ k) (ev σ e ρ k)]
    [(co^ k v)   (co σ k v)]
    [(ap^ f a k) (ap σ f a k)]
    [(ap-op^ o vs k) (ap-op σ o vs k)]
    [(ans^ v) (ans σ v)]))

;; State -> Conf
(define (s->c s)
  (match s
    [(ev _ e ρ k) (ev^ e ρ k)]
    [(co _ k v)   (co^ k v)]
    [(ap _ f a k) (ap^ f a k)]
    [(ap-op _ o vs k) (ap-op^ o vs k)]
    [(ans _ v) (ans^ v)]))

;; Store Store -> Store
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
    (join-store σ (state-σ s))))

;; State^ -> { State^ }
(define (wide-step state)
  (match state
    [(cons cs σ)
     (define ss (for/set ([c cs]) (c->s c σ)))
     (define ss* ((appl step-compiled) ss))
     (set (cons (for/set ([s ss*]) (s->c s))
                (join-stores ss*)))]))

