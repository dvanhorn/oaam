#lang racket
(provide aval^)
(require "ast.rkt"
	 "fix.rkt"
	 "data.rkt")

;; 0CFA in the AAM style, but with a compilation phase, on
;; some hairy Church numeral churning

;; Moral: a simple compilation strategy can eliminate a lot
;; of analysis-time interpretive overhead.


(define-syntax do
  (syntax-rules ()
    [(do [(x se) ...] e)
     (for*/set ([x se] ...)
               e)]))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Compiled" Machine

;; Compile away interpretive overhead of "ev" states

;; Expr -> (Store Env Cont -> State)
(define (compile e)
  (match e
    [(var l x)
     (λ (σ ρ k)
       (do ([v (lookup ρ σ x)])
         (co σ k v)))]
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
       ;; "ev" simulated for push's sake.
       (define-values (σ* a) (push (ev σ (app l e0 e1) ρ k)))
       (c0 σ* ρ (ar c1 ρ a)))]
    [(ife l e0 e1 e2)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (define c2 (compile e2))
     (λ (σ ρ k)       
       (define-values (σ* a) (push (ev σ (ife l e0 e1 e2) ρ k)))
       (c0 σ* ρ (ifk c1 c2 ρ a)))]
    [(1op l o e)
     (define c (compile e))
     (λ (σ ρ k)
       (define-values (σ* a) (push (ev σ (1op l o e) ρ k)))
       (c σ* ρ (1opk o a)))]
    [(2op l o e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (σ ρ k)
       (define-values (σ* a) (push (ev σ (2op l o e0 e1) ρ k)))
       (c0 σ* ρ (2opak o c1 ρ a)))]))


;; "Bytecode" interpreter
;; State -> State
(define (step-compiled s)
  (match s
    [(co σ k v)
     (match k
       ['mt (set (ans σ v))]
       [(ar c ρ l) (c σ ρ (fn v l))]
       [(fn f l)   (do ([k (get-cont σ l)])
                     (ap σ f v k))]
       [(ifk c a ρ l)        
        (for/fold ([s (set)])  ;; Ugly
          ([k (get-cont σ l)])
          (set-union s ((if v c a) σ ρ k)))
        #;
        (do ([k (get-cont σ l)])
          ((if v c a) σ ρ k))]
       [(1opk o l)
        (do ([k (get-cont σ l)])
          (ap-op σ o (list v) k))]
       [(2opak o c ρ l)
        (c σ ρ (2opfk o v l))]
       [(2opfk o u l)
        (do ([k (get-cont σ l)])
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

(define (push s)
  (match s
    [(ev σ e ρ k)
     (define a
       (add1 (for/fold ([i 0])
               ([k (in-hash-keys σ)])
               (max i k))))
     (values (join σ a (set k))
             a)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics
(define (widen b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (bind s)
  (match s
    [(ap σ (clos l x e ρ) v k)
     (values (extend ρ x x)
             (join σ x (set v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (values (extend (extend ρ x x) f f)
             (join (join σ x (set v)) f (set (rlos l f x e ρ))))]))

(define (push s)
  (match s
    [(ev σ e ρ k)
     (define a (exp-lab e))
     (values (join σ a (set k))
             a)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exp -> Set Val
;; 0CFA without store widening
(define (aval e)
  (for/set ([s (fix step-compiled (inj e))]
            #:when (ans? s))
           (ans-v s)))

;; Exp -> Set Vlal
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

;; State^ -> { State^ }
(define (wide-step state)
  (match state
    [(cons cs σ)
     (define ss (for/set ([c cs]) (c->s c σ)))
     (define ss* ((appl step-compiled) ss))
     (set (cons (for/set ([s ss*]) (s->c s))
                (join-stores ss*)))]))


