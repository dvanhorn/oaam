#lang racket
(provide eval eval^ eval/c eval/c^
         lazy-eval lazy-eval^ lazy-eval/c lazy-eval/c^
         0cfa 0cfa^ 0cfa/c 0cfa/c^
         0cfa-step comp-0cfa-step compile-0cfa
         lazy-0cfa lazy-0cfa^ lazy-0cfa/c lazy-0cfa/c^
         1cfa 1cfa^ 1cfa/c 1cfa/c^
         lazy-1cfa lazy-1cfa^ lazy-1cfa/c lazy-1cfa/c^
         widen)
(require "ast.rkt" "fix.rkt" "data.rkt" "env.rkt")

;; TODO
;; - fix wide compile
;; - special fixed

;; A [Rel X ... Y] is a (X -> ... -> (Setof Y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine maker

;; push  : State -> Sto Addr
;; setter  : ?
;; widen : Val -> Val
;; force : [Rel Sto Val Val]
;; delay : [Rel Sto Addr Val]

;; Invariant?  δ is the address of the top frame.

(define (mk-mk-step ev%)
  (λ (push bind setter widen force delay)
    ;; [Rel State State]
    (define (step state)
      (match state
        [(co σ k v)
         (match k
           [(mt) (for*/set ([v (force σ v)])
                             (ans σ v))]
           
           [(ls l '() vs ρ a δ)
            (define args (reverse (cons v vs)))
            (for*/union ((k (get-cont σ a))
                         (f (force σ (first args))))
                      
                      (match f
                        [(clos xs e ρ)
                         (if (= (length xs) (length (rest args)))
                             (let ()
                               (define-values (ρ* σ* δ*) (bind ρ σ l δ xs (rest args)))
                               (ev% σ* e ρ* k δ*))
                             (begin
                               ;(printf "arity mismatch~n")
                               (set)))]
                        [_ (set)]))]
                      
                      
           [(ls l (list-rest e es) vs ρ a δ)
            (ev% σ e ρ (ls l es (cons v vs) ρ a δ) δ)]
           [(ifk t e ρ a δ)
            (for*/union [(k (get-cont σ a))
                         (v (force σ v))]
                        (ev% σ (if v t e) ρ k δ))]
           [(1opk o a)
            (for*/set [(k (get-cont σ a))
                       (v (force σ v))]
                      (ap-op σ o (list v) k))]
           [(2opak o e ρ a δ)
            (ev% σ e ρ (2opfk o v a) δ)]
           [(2opfk o u a)
            (for*/set [(k (get-cont σ a))
                       (v (force σ v))
                       (u (force σ u))]
                      (ap-op σ o (list v u) k))]
           [(lrk x '() '() e ρ a δ)
            (define σ* (join σ (lookup-env ρ x) (force σ v)))
            (for/union ((k (get-cont σ a)))
                       (ev% σ* e ρ k δ))]
           [(lrk x (cons y xs) (cons e es) b ρ a δ)
            (define σ* (join σ (lookup-env ρ x) (force σ v)))            
            (ev% σ* e ρ (lrk y xs es b ρ a δ) δ)]
           [(sk! l a)
            (define σ* (setter σ l v))
            (for/set ((k (get-cont σ a)))
                     (co σ* k (void)))])]
                       
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
        
        ;; this code is dead when running compiled code.
        [(ev σ e ρ k δ)
         (match e
           [(var l x)           (for/set ((v (delay σ (lookup-env ρ x))))
                                         (co σ k v))]
           [(num l n)           (set (co σ k n))]
           [(bln l b)           (set (co σ k b))]
           [(lam l x e)         (set (co σ k (clos x e ρ)))]
           [(lrc l xs es b)
            (define-values (σ0 a) (push σ l δ k))            
            (define as (map (λ (x) (cons x δ)) xs))
            (define ρ* (extend* ρ xs as))
            (define σ* (join* σ0 as (map (λ _ (set)) xs)))
            (set (ev σ* (first es) ρ* (lrk (first xs) (rest xs) (rest es) b ρ* a δ) δ))]
           [(app l e0 es)
            (define-values (σ* a) (push σ l δ k))
            (set (ev σ* e0 ρ (ls l es '() ρ a δ) δ))]
           [(ife l e0 e1 e2)
            (define-values (σ* a) (push σ l δ k))
            (set (ev σ* e0 ρ (ifk e1 e2 ρ a δ) δ))]
           [(1op l o e0)
            (define-values (σ* a) (push σ l δ k))
            (set (ev σ* e0 ρ (1opk o a) δ))]
           [(2op l o e0 e1)
            (define-values (σ* a) (push σ l δ k))
            (set (ev σ* e0 ρ (2opak o e1 ρ a δ) δ))]
           [(st! l x e0)
            (define-values (σ* a) (push σ l δ k))
            (set (ev σ* e0 ρ (sk! (lookup-env ρ x) a) δ))])]
        
        [_ (set)]))
    step))


(define ((push K) σ l δ k)
  (define a (cons l δ))
  (values (join σ a (set k))
          a))

(define ((bind K) ρ σ l δ xs vs)
  (define δ* (truncate (cons l δ) K))
  (define as (map (λ (x) (cons x δ*)) xs))  
  (define ρ* (extend* ρ xs as))
  (define σ* (join* σ as (map (λ (v) (force σ v)) vs)))
  (values ρ* σ* δ*))

(define (ev-interp  σ e ρ k δ) (set (ev σ e ρ k δ)))
(define (ev-compile σ c ρ k δ) (c σ ρ k δ))
 
(define mk-step  (mk-mk-step ev-interp))

(define (mk-comp-step push bind setter widen force delay)
  (values (mk-step push bind setter widen force delay)
          (mk-comp push delay)
          ((mk-mk-step ev-compile) push bind setter widen force delay)))

(define (mk-comp push delay)
  ;; Expr -> (Store Env Cont Contour -> State)
  (define (compile e)
    (match e
      [(var l x)
       (λ (σ ρ k δ)
         (for/set ((v (delay σ (lookup-env ρ x))))
                  (co σ k v)))]
      [(num l n) (λ (σ ρ k δ) (set (co σ k n)))]
      [(bln l b) (λ (σ ρ k δ) (set (co σ k b)))]
      [(lam l x e)
       (define c (compile e))
       (λ (σ ρ k δ) (set (co σ k (clos x c ρ))))]   
    [(lrc l xs es b)
     (define c (compile (first es)))
     (define cs (map compile (rest es)))
     (define cb (compile b))
     (define x (first xs))
     (define xs* (rest xs))
     (define ss (map (λ _ (set)) xs))
     (λ (σ ρ k δ)
       (define-values (σ0 a) (push σ l δ k))            
       (define as (map (λ (x) (cons x δ)) xs))
       (define ρ* (extend* ρ xs as))
       (define σ* (join* σ0 as (map (λ _ (set)) xs)))
       (c σ* ρ* (lrk x xs* cs cb ρ* a δ) δ))]
    [(app l e es)
     (define c (compile e))
     (define cs (map compile es))
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c σ* ρ (ls l cs '() ρ a δ) δ))]
    [(ife l e0 e1 e2)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (define c2 (compile e2))
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c0 σ* ρ (ifk c1 c2 ρ a δ) δ))]
    [(1op l o e)
     (define c (compile e))
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c σ* ρ (1opk o a) δ))]   
    [(2op l o e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c0 σ* ρ (2opak o c1 ρ a δ) δ))]   
    [(st! l x e)
     (define c (compile e))         
     (λ (σ ρ k δ)
       (define-values (σ* a) (push σ l δ k))
       (c σ* ρ (sk! (lookup-env ρ x) a) δ))]))
  compile)
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Primops

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
 

(define (mk-eval-setter force)
  (λ (σ l v) (extend σ l (force σ v))))

(define (mk-kcfa-setter force)
  (λ (σ l v) (join σ l (force σ v))))

(define (force σ x)
  (match x
    [(addr a) (lookup-sto σ a)]
    [v (set v)]))

(define strict-eval-setter
  (mk-eval-setter (λ (_ v) (set v))))

(define lazy-eval-setter
  (mk-eval-setter force))
  
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define (truncate δ k)
  (cond [(zero? k) '()]
        [(empty? δ) '()]
        [else
         (cons (first δ)
               (truncate (rest δ) (sub1 k)))]))

(define (widen b)
  (match b
    [(? number?) 'number]
    [(? boolean?) b]
    ['number 'number]
    [else (error "Unknown base value" b)]))


(define (delay σ x)
  (set (addr x)))

(define strict-kcfa-setter
  (mk-kcfa-setter (λ (_ v) (set v))))

(define lazy-kcfa-setter
  (mk-kcfa-setter force))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of transition relations

(define-values (eval-step compile-eval comp-eval-step)
  (mk-comp-step (push +inf.0)
                (bind +inf.0)
                strict-eval-setter
                eval-widen
                (lambda (σ x) (set x))
                lookup-sto))

(define-values (lazy-eval-step compile-lazy-eval comp-lazy-eval-step)
  (mk-comp-step (push +inf.0)
                (bind +inf.0)
                strict-eval-setter
                eval-widen
                force
                delay))

(define-values (1cfa-step compile-1cfa comp-1cfa-step)
  (mk-comp-step (push 1)
                (bind 1)
                strict-kcfa-setter
                widen
                (lambda (σ x) (set x))
                lookup-sto))

(define-values (lazy-1cfa-step compile-lazy-1cfa comp-lazy-1cfa-step)
  (mk-comp-step (push 1)
                (bind 1)
                lazy-kcfa-setter
                widen
                force
                delay))

(define-values (0cfa-step compile-0cfa comp-0cfa-step)
  (mk-comp-step (push 0)
                (bind 0)
                strict-kcfa-setter
                widen
                (lambda (σ x) (set x))
                lookup-sto))

(define-values (lazy-0cfa-step compile-lazy-0cfa comp-lazy-0cfa-step)
  (mk-comp-step (push 0)
                (bind 0)
                lazy-kcfa-setter
                widen
                force
                delay))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators

(define ((mk-aval step inj) e)
  (for/set ([s (fix step (inj e))]
            #:when (ans? s))
           (ans-v s)))

;; (State -> Setof State) -> Exp -> Set Val
;; 0CFA without store widening

;; (State^ -> Setof State^) -> Exp -> Set Val
;; 0CFA with store widening
(define ((mk-aval^ step inj) e)
  (for/fold ([vs (set)])
    ([s (fix (wide-step step) (inj e))])
    (set-union vs
               (match s
                 [(cons cs σ)
                  (for/set ([c cs]
                            #:when (ans^? c))
                           (ans^-v c))]))))

(define k0 (mt))
(define ε '())

;; Exp -> Set State
(define (inj e)
  (set (ev (hash) e (hash) k0 ε)))

;; Exp -> Set State^
(define (inj-wide e)
  (set (cons (set (ev^ e (hash) k0 ε)) (hash))))

(define ((inj/c c) e)
  ((c e) (hash) (hash) k0 ε))

(define ((inj-wide/c c) e)
  (for/set ((s (in-set ((c e) (hash) (hash) k0 ε))))
           (cons (set (s->c s)) (state-σ s))))

(define (mk-evals step comp-step compile)
  (values (mk-aval  step inj)
          (mk-aval^ step inj-wide)
          (mk-aval  comp-step (inj/c compile))
          (mk-aval^ comp-step (inj-wide/c compile))))

(define-values (eval eval^ eval/c eval/c^)
  (mk-evals eval-step comp-eval-step compile-eval))

(define-values (lazy-eval lazy-eval^ lazy-eval/c lazy-eval/c^)
  (mk-evals lazy-eval-step comp-lazy-eval-step compile-lazy-eval))

(define-values (0cfa 0cfa^ 0cfa/c 0cfa/c^)
  (mk-evals 0cfa-step comp-0cfa-step compile-0cfa))

(define-values (lazy-0cfa lazy-0cfa^ lazy-0cfa/c lazy-0cfa/c^)
  (mk-evals lazy-0cfa-step comp-lazy-0cfa-step compile-lazy-0cfa))

(define-values (1cfa 1cfa^ 1cfa/c 1cfa/c^)
  (mk-evals 1cfa-step comp-1cfa-step compile-1cfa))

(define-values (lazy-1cfa lazy-1cfa^ lazy-1cfa/c lazy-1cfa/c^)
  (mk-evals lazy-1cfa-step comp-lazy-1cfa-step compile-lazy-1cfa))


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
