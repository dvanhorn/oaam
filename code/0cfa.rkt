#lang racket
(provide aval^ eval)
(require "ast.rkt" "fix.rkt" "data.rkt")

;; 0CFA in the AAM style on some hairy Church numeral churning

;; Moral: per machine-state store polyvariance is not viable,
;; but with widening it's not so bad.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine

(define (mk-step push bind widen)
  ;; [Relation State State]
  (define (step state)
    (match state
      [(ev σ e ρ k)
       (match e
         [(var l x)           (for/set ((v (lookup ρ σ x)))
                                (co σ k v))]
         [(num l n)           (set (co σ k n))]
         [(bln l b)           (set (co σ k b))]         
         [(lam l x e)         (set (co σ k (clos l x e ρ)))]         
         [(rec f (lam l x e)) (set (co σ k (rlos l f x e ρ)))]
         [(lrc l xs es b)
          (define-values (σ0 a) (push state))
          (define-values (ρ* σ*) (bind (ev σ0 e ρ k)))
          (set (ev σ* (first es) ρ* (lrk (first xs) (rest xs) (rest es) b ρ* a)))]
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
         ['mt (set (ans σ v))]
         [(ar e ρ l) (set (ev σ e ρ (fn v l)))]
         [(fn f l)   (for/set ((k (get-cont σ l)))
                       (ap σ f v k))]
         [(ifk c a ρ l)
          (for/set ((k (get-cont σ l)))
            (ev σ (if v c a) ρ k))]
         [(1opk o l)
          (for/set ((k (get-cont σ l)))
            (ap-op σ o (list v) k))]
         [(2opak o e ρ l)
          (set (ev σ e ρ (2opfk o v l)))]
         [(2opfk o u l)
          (for/set ((k (get-cont σ l)))
            (ap-op σ o (list v u) k))]
         [(lrk x '() '() e ρ l)
          (define-values (_ σ*) (bind state))
          (for/set ((k (get-cont σ l)))
            (ev σ* e ρ k))]
         [(lrk x (cons y xs) (cons e es) b ρ a)
          (define-values (_ σ*) (bind state))          
          (set (ev σ* e ρ (lrk y xs es b ρ a)))])]
          

      [(ap σ fun a k)
       (match fun
         [(clos l x e ρ)
          (define-values (ρ* σ*) (bind state))
          (set (ev σ* e ρ* k))]
         [(rlos l f x e ρ)
          (define-values (ρ* σ*) (bind state))
          (set (ev σ* e ρ* k))]
         [_ (set)])]

      [(ap-op σ o vs k)
       (match* (o vs)
         [('zero? (list (? number? n))) (set (co σ k (zero? n)))]
         [('zero? (list 'number))
          (set (co σ k #t)
               (co σ k #f))]
         [('not (list #t))  (set (co σ k #f))]
         [('not (list #f))  (set (co σ k #t))]
         [('= (list (? number? n) (? number? m)))
          (set (co σ k (= n m)))]
         [((? z->z? o) (list x))
          (for/set ((v (z->z o x)))
                   (co σ k (widen v)))]         
         [((? z-z->z? o) (list x y))
          (for/set ((v (z-z->z o x y)))
                   (co σ k (widen v)))]
         [(_ _) (set)])]

      [_ (set)]))

  step)

(define (z->z? o)
  (memq o '(add1 sub1)))

(define (z->z o x)
  (match* (o x)
    [(o 'number) (set 'number)]
    [(o (? number? n))
     (set (case o
            [(add1) (add1 n)]
            [(sub1) (sub1 n)]))]            
    [(o _) (set)]))

(define (z-z->z? o)
  (memq o '(+ - *)))

(define (z-z->z o x y)
  (match* (o x y)
    [(o 'number 'number) (set 'number)]
    [(o 'number (? number?)) (set 'number)]
    [(o (? number?) 'number) (set 'number)]
    [(o (? number? n) (? number? m))
     (set (case o
            [(+) (+ n m)]
            [(-) (- n m)]
            [(*) (* n m)]))]
    [(o _ _) (set)]))
          
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete semantics

(define (eval-widen b)
  (cond [(number? b) b]
        [else (error "Unknown base value" b)]))

(define (eval-bind s)
  (define (next-addr σ)
    (add1 (for/fold ([i 0])
            ([k (in-hash-keys σ)])
            (max i k))))
  (match s
    [(co σ (lrk x xs es e ρ k) v)
     (define a (lookup-env ρ x))
     (values ρ (join-one σ a v))]
    
    [(ev σ (lrc l xs es b) ρ k)
     (define a (next-addr σ))
     (define as (for/list ([i (in-range (length xs))])
                  (+ a i)))
     (values (extend* ρ xs as)
             (join* σ as (map (λ _ (set)) xs)))]
    
    [(ap σ (clos l x e ρ) v k)
     (define a (next-addr σ)) 
     (values (extend ρ x a)
             (extend σ a (set v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (define a (next-addr σ))
     (define b (add1 a))
     (values (extend (extend ρ x a) f b)
             (join (join σ a (set v)) b (set (rlos l f x e ρ))))]))

(define (eval-push s)
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
    [(co σ (lrk x xs es e ρ a) v)
     (values ρ (join-one σ x v))]
    [(ev σ (lrc l xs es b) ρ k)
     (values (extend* ρ xs xs)
             (join* σ xs (map (λ _ (set)) xs)))]
    [(ap σ (clos l x e ρ) v k)
     (values (extend ρ x x)
             (join-one σ x v))]
    [(ap σ (rlos l f x e ρ) v k)
     (values (extend (extend ρ x x) f f)
             (join-one (join-one σ x v) f (rlos l f x e ρ)))]))

(define (push s)
  (match s
    [(ev σ e ρ k)
     (define a (exp-lab e))
     (values (join σ a (set k))
             a)]))

(define step (mk-step push bind widen))
(define eval-step (mk-step eval-push eval-bind eval-widen))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exp -> Set Val
;; 0CFA without store widening
(define (aval e)
  (for/set ([s (fix step (inj e))]
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

;; Exp -> { Val }
;; Eval with infinite store
(define (eval e)
  (for/set ([s (fix eval-step (inj e))]
            #:when (ans? s))
           (ans-v s)))

;; Exp -> Set State
(define (inj e)
  (set (ev (hash) e (hash) 'mt)))

;; Exp -> Set State^
(define (inj-wide e)
  (set (cons (set (ev^ e (hash) 'mt)) (hash))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ = (cons (Set Conf) Store)

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
     (define ss* ((appl step) ss))
     (set (cons (for/set ([s ss*]) (s->c s))
                (join-stores ss*)))]))

