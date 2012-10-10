#lang racket
(provide eval aval aval^
         lazy-eval lazy-aval lazy-aval^
         widen)
(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt")

;; TODO
;; - compile
;; - special fixed

;; A [Rel X ... Y] is a (X -> ... -> (Setof Y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

;; push  : State -> Sto Addr
;; bind  : State -> Env Sto
;; widen : Val -> Val
;; force : [Rel Sto Val Val]
;; delay : [Rel Sto Addr Val]

;; Invariant?  δ is the address of the top frame.

(define (ev% σ e ρ k δ)
  (set (ev σ e ρ k δ)))

(define (mk-step push bind widen force delay)
  ;; [Rel State State]
  (define (step state)
    (match state
      [(ev σ e ρ k δ)
       (match e
         [(var l x)           (for/set ((v (delay σ (lookup-env ρ x))))
                                (co σ k v))]
         [(num l n)           (set (co σ k n))]
         [(bln l b)           (set (co σ k b))]
         [(lam l x e)         (set (co σ k (clos l x e ρ)))]
         [(lrc l xs es b)
          (define-values (σ0 a) (push state))
          (define-values (ρ* σ*) (bind (ev σ0 e ρ k δ)))
          (set (ev σ* (first es) ρ* (lrk (first xs) (rest xs) (rest es) b ρ* a) δ))]
         [(app l e es)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (ls es '() ρ a) δ))]
         [(ife l e0 e1 e2)
          (define-values (σ* a) (push state))
          (set (ev σ* e0 ρ (ifk e1 e2 ρ a) δ))]
         [(1op l o e)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (1opk o a) δ))]
         [(2op l o e f)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (2opak o f ρ a) δ))]
         [(st! l x e)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (sk! (lookup-env ρ x) a) δ))])]

      [(co σ k v)
       (match k
         ['mt (for*/set ([v (force σ v)])
                        (ans σ v))]
         [(ls '() vs ρ l)
          (define as (reverse (cons v vs)))
          (for*/set ((k (get-cont σ l))
                     (f (force σ (first as))))
                    (ap σ f (rest as) k l))]
         [(ls (list-rest e es) vs ρ l)
          (ev% σ e ρ (ls es (cons v vs) ρ l) l)]
         [(ifk c a ρ δ)
          (for*/union [(k (get-cont σ δ))
                     (v (force σ v))]
            (ev% σ (if v c a) ρ k δ))]
         [(1opk o l)
          (for*/set [(k (get-cont σ l))
                     (v (force σ v))]
            (ap-op σ o (list v) k))]
         [(2opak o e ρ l)
          (ev% σ e ρ (2opfk o v l) l)]
         [(2opfk o u l)
          (for*/set [(k (get-cont σ l))
                     (v (force σ v))
                     (u (force σ u))]
            (ap-op σ o (list v u) k))]
         [(lrk x '() '() e ρ δ)
          (define-values (_ σ*) (bind state))
          (for/union ((k (get-cont σ δ)))
            (ev% σ* e ρ k δ))]
         [(lrk x (cons y xs) (cons e es) b ρ δ)
          (define-values (_ σ*) (bind state))
          (ev% σ* e ρ (lrk y xs es b ρ δ) δ)]
         [(sk! l δ)
          (define-values (_ σ*) (bind state))
          (for/set ((k (get-cont σ δ)))
            (co σ* k (void)))])]

      [(ap σ fun as k δ)
       (match fun
         [(clos l xs e ρ)
          (define-values (ρ* σ*) (bind state))
          (ev% σ* e ρ* k δ)]
         [_ (set)])]

      [(ap-op σ o vs k)
       (match* (o vs)
         [('zero? (list (? number? n))) (set (co σ k (zero? n)))]
         [('zero? (list 'number))
          (set (co σ k #t)
               (co σ k #f))]
         [('symbol? 'symbol)  (set (co σ k #t))]
         [('string? (list v)) (set (co σ k (symbol? v)))]
         [('string? 'string)  (set (co σ k #t))]
         [('string? (list v)) (set (co σ k (string? v)))]
         [('not (list #t))  (set (co σ k #f))]
         [('not (list #f))  (set (co σ k #t))]
	 [('string=? (list (? string? s1) (? string? s2)))
          (set (co σ k (string=? s1 s2)))]
         [('string=? (list (? stringish? s1) (? stringish? s2)))
          (set (co σ k #t)
               (co σ k #t))]
         [('= (list (? number? n) (? number? m)))
          (set (co σ k (= n m)))]
         [('= (list (? number? n) 'number))
          (set (co σ k #t)
               (co σ k #f))]
         [('= (list 'number (? number? n)))
          (set (co σ k #t)
               (co σ k #f))]
         [('= (list 'number 'number))
          (set (co σ k #t)
               (co σ k #f))]
         [((? z->z? o) (list x))
          (for/set ((v (z->z o x)))
                   (co σ k (widen v)))]
         [((? z-z->z? o) (list x y))
          (for/set ((v (z-z->z o x y)))
                   (co σ k (widen v)))]
         [(_ _) (set)])]

      [_ (set)]))

  step)


(define (truncate δ k)
  (cond [(zero? k) '()]
        [(empty? δ) '()]
        [else
         (cons (first δ)
               (truncate (rest δ) (sub1 k)))]))

(define (stringish? x)
  (or (string? x)
      (eq? 'string x)))  

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
        [(boolean? b) b]
        [else (error "Unknown base value" b)]))


(define ((mk-eval-bind force) s)
  (match s
    [(co σ (sk! l a) v)
     ;; empty env says this is the wrong place for this.
     (values (hash) (extend σ l (force σ v)))]
    [(co σ (lrk x xs es e ρ δ) v)
     (define a (lookup-env ρ x))
     (values ρ (join σ a (force σ v)))]
    [(ev σ (lrc l xs es b) ρ k δ)
     (define as (map (λ (x) (cons x δ)) xs))
     (values (extend* ρ xs as)
             (join* σ as (map (λ _ (set)) xs)))]
    [(ap σ (clos l xs e ρ) vs k δ)
     (define as (map (λ (x) (cons x δ)) xs))
     (values (extend* ρ xs as)
             (extend* σ as (map (λ (v) (force σ v)) vs)))]))

(define ((mk-0cfa-bind force) s)
  (match s
    [(co σ (sk! l a) v)
     ;; empty env says this is the wrong place for this.
     (values (hash) (join σ l (force σ v)))]
    [(co σ (lrk x xs es e ρ a) v)
     (define a (lookup-env ρ x))
     (values ρ (join σ a (force σ v)))]
    [(ev σ (lrc l xs es b) ρ k δ)
     (define as (map (λ (x) (cons x δ)) xs))
     (values (extend* ρ xs as)
             (join* σ as (map (λ _ (set)) xs)))]
    [(ap σ (clos l xs e ρ) vs k δ)
     (define as (map (λ (x) (cons x δ)) xs))
     (values (extend* ρ xs as)
             (extend* σ as (map (λ (v) (force σ v)) vs)))]))

(define (force σ x)
  (match x
    [(addr a) (lookup-sto σ a)]
    [v (set v)]))

(define strict-eval-bind (mk-eval-bind (λ (_ v) (set v))))
(define lazy-eval-bind   (mk-eval-bind force))



(define ((push K) s)
  (match s
    [(ev σ e ρ k δ)
     (define a (cons (exp-lab e) (truncate δ K)))
     (values (join σ a (set k))
             a)]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define (widen b)
  (match b
    [(? number?) 'number]
    [(? boolean?) b]
    ['number 'number]
    [else (error "Unknown base value" b)]))


(define (delay σ x)
  (set (addr x)))

(define strict-0cfa-bind (mk-0cfa-bind (λ (_ v) (set v))))
(define lazy-0cfa-bind   (mk-0cfa-bind force))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of transition relations

(define 0cfa-step
  (mk-step (push 0)
           strict-0cfa-bind
           widen
           (lambda (σ x) (set x))
           lookup-sto))

(define eval-step
  (mk-step (push +inf.0)
           strict-eval-bind
           eval-widen
           (lambda (σ x) (set x))
           lookup-sto))

(define lazy-eval-step
  (mk-step (push +inf.0)
           lazy-eval-bind
           eval-widen
           force
           delay))

(define lazy-0cfa-step
  (mk-step (push 0)
           lazy-0cfa-bind
           widen
           force
           delay))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators

;; (State -> Setof State) -> Exp -> Set Val
;; 0CFA without store widening
(define ((mk-aval step) e)
  (for/set ([s (fix step (inj e))]
            #:when (ans? s))
           (ans-v s)))

;; (State^ -> Setof State^) -> Exp -> Set Val
;; 0CFA with store widening
(define ((mk-aval^ step) e)
  (for/fold ([vs (set)])
    ([s (fix (wide-step step) (inj-wide e))])
    (set-union vs
               (match s
                 [(cons cs σ)
                  (for/set ([c cs]
                            #:when (ans^? c))
                           (ans^-v c))]))))

(define eval       (mk-aval  eval-step))
(define eval^      (mk-aval^ eval-step))
(define lazy-eval  (mk-aval  lazy-eval-step))
(define aval       (mk-aval  0cfa-step))
(define aval^      (mk-aval^ 0cfa-step))
(define lazy-aval^ (mk-aval^ lazy-0cfa-step))
(define lazy-aval  (mk-aval  lazy-0cfa-step))


;; Exp -> Set State
(define (inj e)
  (ev% (hash) e (hash) 'mt '()))

;; Exp -> Set State^
(define (inj-wide e)
  (set (cons (set (ev^ e (hash) 'mt '())) (hash))))


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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for/union

(define-syntax-rule (for/union guards body1 body ...)
  (for/fold ([res (set)]) guards (set-union res (let () body1 body ...))))
(define-syntax-rule (for*/union guards body1 body ...)
  (for*/fold ([res (set)]) guards (set-union res (let () body1 body ...))))

