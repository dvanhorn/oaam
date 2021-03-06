#lang racket
(provide aval^)
(require "ast.rkt" "data.rkt")

;; 0CFA in the AAM style on some hairy Church numeral churning
;; using lazy non-determinism (wait until your in demand before
;; forking).

;; (X -> Set X) -> (Set X) -> (Set X)
(define ((appl f) s)
  (for/fold ([i (set)])
    ([x (in-set s)])
    (set-union i (f x))))

;; (X -> Set X) (Set X) -> (Set X)
;; Calculate fixpoint of (appl f).
(define (fix f s)
  (let loop ((accum (set)) (front s))
    (if (set-empty? front)
        accum
        (let ((new-front ((appl f) front)))
          (loop (set-union accum front)
                (set-subtract new-front accum))))))

(define-syntax do
  (syntax-rules ()
    [(do [(x se) ...] e)
     (for*/set ([x se] ...)
               e)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine

#;(struct addr (a) #:transparent)
;; Store (Addr + Val) -> Set Val
(define (get-val σ v)
  (match v
    [(addr loc) (hash-ref σ loc (λ () (error "~a ~a" loc σ)))]
    [_ (set v)]))

;; State -> Set State
(define (step state)
  ;(printf "~a~n" state)
  (match state
    [(ev σ e ρ k)
     (match e
       [(var l x)           (set (co σ k (addr (lookup-env ρ x))))]
       [(num l n)           (set (co σ k n))]
       [(bln l b)           (set (co σ k b))]
       [(lam l x e)         (set (co σ k (clos l x e ρ)))]
       [(rec f (lam l x e)) (set (co σ k (rlos l f x e ρ)))]
       [(app l f e)
        (define-values (σ* a) (push state))
        (set (ev σ* f ρ (ar e ρ a)))]
       [(ife l e0 e1 e2)
        (define-values (σ* a) (push state))
        (set (ev σ* e0 ρ (ifk e1 e2 ρ a)))]
       [(1op l o e)
        (define-values (σ* a) (push state))
        (set (ev σ* e ρ (1opk o a)))]
       [(2op l o e f)
        (define-values (σ* a) (push state))
        (set (ev σ* e ρ (2opak o f ρ a)))])]

    [(co σ k v)
     (match k
       ['mt (do ((v (get-val σ v)))
              (ans σ v))]
       [(ar e ρ l) (set (ev σ e ρ (fn v l)))]
       [(fn f l)
        (do ([k (get-cont σ l)]
             [f (get-val σ f)])                     
          (ap σ f v k))]       
       [(ifk c a ρ l)
        (do ([k (get-cont σ l)]
             [v (get-val σ v)])
          (ev σ (if v c a) ρ k))]        
       [(1opk o l)
        (do ([k (get-cont σ l)]
             [v (get-val σ v)])
          (ap-op σ o (list v) k))]
       [(2opak o e ρ l)
        (set (ev σ e ρ (2opfk o v l)))]
       [(2opfk o u l)
        (do ([k (get-cont σ l)]
             [v (get-val σ v)]
             [u (get-val σ u)])
          (ap-op σ o (list v u) k))])]
 
    [(ap σ fun a k)
     (match fun
       [(clos l x e ρ)
        (define-values (ρ* σ*) (bind state))
        (set (ev σ* e ρ* k))]
       [(rlos l f x e ρ)
        (define-values (ρ* σ*) (bind state))
        (set (ev σ* e ρ* k))]
       [_ (set state)])]

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
       [(_ _) (set state)])]

    [_ (set state)]))


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
             (extend σ a (get-val σ v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (define a
       (add1 (for/fold ([i 0])
               ([k (in-hash-keys σ)])
               (max i k))))
     (define b (add1 a))
     (values (extend (extend ρ x a) f b)
             (join (join σ a (get-val σ v)) b (set (rlos l f x e ρ))))]))

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
             (extend σ x (get-val σ v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (values (extend (extend ρ x x) f f)
             (join (join σ x (get-val σ v)) f (set (rlos l f x e ρ))))]))

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
  (for/set ([s (fix step (inj e))]
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
  (set (ev (hash) e (hash) 'mt)))

;; Exp -> Set State^
(define (inj-wide e)
  (set (cons (set (ev^ e (hash) 'mt)) (hash))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ = (cons (Set Conf) Store)

;; State^ -> { State^ }
(define (wide-step state)
  (match state
    [(cons cs σ)
     (define ss (for/set ([c cs]) (c->s c σ)))
     (define ss* ((appl step) ss))
     (set (cons (for/set ([s ss*]) (s->c s))
                (join-stores ss*)))]))


