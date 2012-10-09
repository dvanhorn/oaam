#lang racket
(provide eval aval aval^
         lazy-eval lazy-aval lazy-aval^
         widen)
(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt")

;; A [Rel X ... Y] is a (X -> ... -> (Setof Y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

;; push  : State -> Sto Addr
;; bind  : State -> Env Sto
;; widen : Val -> Val
;; force : [Rel Sto Val Val]
;; delay : [Rel Sto Addr Val]

(define (mk-step push bind widen force delay)
  ;; [Rel State State]
  (define (step state)
    (match state
      [(ev σ e ρ k)
       (match e
         [(var l x)           (for/set ((v (delay σ (lookup-env ρ x))))
                                (co σ k v))]
         [(num l n)           (set (co σ k n))]
         [(bln l b)           (set (co σ k b))]
         [(lam l x e)         (set (co σ k (clos l x e ρ)))]
         [(lrc l xs es b)
          (define-values (σ0 a) (push state))
          (define-values (ρ* σ*) (bind (ev σ0 e ρ k)))
          (set (ev σ* (first es) ρ* (lrk (first xs) (rest xs) (rest es) b ρ* a)))]
         [(app l e es)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (ls es '() ρ a)))]
         [(ife l e0 e1 e2)
          (define-values (σ* a) (push state))
          (set (ev σ* e0 ρ (ifk e1 e2 ρ a)))]
         [(1op l o e)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (1opk o a)))]
         [(2op l o e f)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (2opak o f ρ a)))]
         [(st! l x e)
          (define-values (σ* a) (push state))
          (set (ev σ* e ρ (sk! (lookup-env ρ x) a)))])]

      [(co σ k v)
       (match k
         ['mt (for*/set ([v (force σ v)])
                        (ans σ v))]
         [(ls '() vs ρ l)
          (define as (reverse (cons v vs)))
          (for*/set ((k (get-cont σ l))
                     (f (force σ (first as))))
                    (ap σ f (rest as) k))]
         [(ls (list-rest e es) vs ρ l)
          (set (ev σ e ρ (ls es (cons v vs) ρ l)))]
         [(ifk c a ρ l)
          (for*/set [(k (get-cont σ l))
                     (v (force σ v))]
            (ev σ (if v c a) ρ k))]
         [(1opk o l)
          (for*/set [(k (get-cont σ l))
                     (v (force σ v))]
            (ap-op σ o (list v) k))]
         [(2opak o e ρ l)
          (set (ev σ e ρ (2opfk o v l)))]
         [(2opfk o u l)
          (for*/set [(k (get-cont σ l))
                     (v (force σ v))
                     (u (force σ u))]
            (ap-op σ o (list v u) k))]
         [(lrk x '() '() e ρ l)
          (define-values (_ σ*) (bind state))
          (for/set ((k (get-cont σ l)))
            (ev σ* e ρ k))]
         [(lrk x (cons y xs) (cons e es) b ρ a)
          (define-values (_ σ*) (bind state))
          (set (ev σ* e ρ (lrk y xs es b ρ a)))]
         [(sk! l a)
          (define-values (_ σ*) (bind state))
          (for/set ((k (get-cont σ a)))
            (co σ* k (void)))])]

      [(ap σ fun as k)
       (match fun
         [(clos l xs e ρ)
          (define-values (ρ* σ*) (bind state))
          (set (ev σ* e ρ* k))]
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
  (define (next-addr σ)
    (add1 (for/fold ([i 0])
            ([k (in-hash-keys σ)])
            (max i k))))
  (match s
    [(co σ (sk! l a) v)
     ;; empty env says this is the wrong place for this.
     (values (hash) (extend σ l (force σ v)))]
    [(co σ (lrk x xs es e ρ k) v)
     (define a (lookup-env ρ x))
     (values ρ (join-one σ a v))]
    [(ev σ (lrc l xs es b) ρ k)
     (define a (next-addr σ))
     (define as (for/list ([i (in-range (length xs))])
                  (+ a i)))
     (values (extend* ρ xs as)
             (join* σ as (map (λ _ (set)) xs)))]
    [(ap σ (clos l xs e ρ) vs k)
     (define a (next-addr σ))
     (define as (for/list ([i (in-range (length xs))])
                  (+ a i)))
     (values (extend* ρ xs as)
             (extend* σ as (map set vs)))]))

(define (force σ x)
  (match x
    [(addr a) (lookup-sto σ a)]
    [v (set v)]))

(define strict-eval-bind (mk-eval-bind (λ (_ v) (set v))))
(define lazy-eval-bind   (mk-eval-bind force))

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
  (match b
    [(? number?) 'number]
    [(? boolean?) b]
    ['number 'number]
    [else (error "Unknown base value" b)]))

(define ((mk-0cfa-bind force) s)
  (match s
    [(co σ (sk! l a) v)
     ;; empty env says this is the wrong place for this.
     (values (hash) (join σ l (force σ v)))]
    [(co σ (lrk x xs es e ρ a) v)
     (values ρ (join σ x (force σ v)))]
    [(ev σ (lrc l xs es b) ρ k)
     (values (extend* ρ xs xs)
             (join* σ xs (map (λ _ (set)) xs)))]
    [(ap σ (clos l xs e ρ) vs k)
     (values (extend* ρ xs xs)
             (join* σ xs (map (λ (v) (force σ v)) vs)))]))

(define (push s)
  (match s
    [(ev σ e ρ k)
     (define a (exp-lab e))
     (values (join σ a (set k))
             a)]))

(define (delay σ x)
  (set (addr x)))

(define strict-0cfa-bind (mk-0cfa-bind (λ (_ v) (set v))))
(define lazy-0cfa-bind   (mk-0cfa-bind force))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of transition relations

(define 0cfa-step
  (mk-step push
           strict-0cfa-bind
           widen
           (lambda (σ x) (set x))
           lookup-sto))

(define eval-step
  (mk-step eval-push
           strict-eval-bind
           eval-widen
           (lambda (σ x) (set x))
           lookup-sto))

(define lazy-eval-step
  (mk-step eval-push
           lazy-0cfa-bind
           eval-widen
           force
           delay))

(define lazy-0cfa-step
  (mk-step push
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
  (set (ev (hash) e (hash) 'mt)))

;; Exp -> Set State^
(define (inj-wide e)
  (set (cons (set (ev^ e (hash) 'mt)) (hash))))


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

