#lang racket
(provide aval^ widen)
(require "ast.rkt"
         (except-in "data.rkt" get-cont ap^ ap-op^)
         "progs.rkt"
         (for-syntax syntax/parse))

(define-syntax-rule (for/union guards body1 body ...)
  (for/fold ([res (set)]) guards (set-union res (let () body1 body ...))))
(define-syntax-rule (for*/union guards body1 body ...)
  (for*/fold ([res (set)]) guards (set-union res (let () body1 body ...))))

;; 0CFA in the AAM style on some hairy Church numeral churning

;; + compilation phase
;; + lazy non-determinism
;; + specialized step & iterator

;; State  = (cons Conf Store)
;; State^ = (cons (Set Conf) Store)

;; Comp = Store Env Cont -> State^

;; Global store
(define σ #f)
(define unions 0)
(define todo '())
(define seen #f)

(define (get-cont σ l)
  (vector-ref σ l))

(define (yield s)
  (unless (= unions (hash-ref seen s -1))
    (hash-set! seen s unions)
    (set! todo (cons s todo))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Compiled" Machine

;; Compile away interpretive overhead of "ev" states

;; Expr -> Comp
(define (compile e)
  (match e
    [(var l x)
     (λ (ρ k)
       (yield (co^ k (addr (lookup-env ρ x)))))]
    [(num l n)   (λ (ρ k) (yield (co^ k n)))]
    [(bln l b)   (λ (ρ k) (yield (co^ k b)))]
    [(lam l x e)
     (define c (compile e))
     (λ (ρ k) (yield (co^ k (clos l x c ρ))))]
    [(rec f (lam l x e))
     (define c (compile e))
     (λ (ρ k) (yield (co^ k (rlos l f x c ρ))))]
    [(app l e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (ρ k)
       (define a (push l ρ k))
       (c0 ρ (ar c1 ρ a)))]
    [(ife l e0 e1 e2)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (define c2 (compile e2))
     (λ (ρ k)
       (define a (push l ρ k))
       (c0 ρ (ifk c1 c2 ρ a)))]
    [(1op l o e)
     (define c (compile e))
     (λ (ρ k)
       (define a (push l ρ k))
       (c ρ (1opk o a)))]
    [(2op l o e0 e1)
     (define c0 (compile e0))
     (define c1 (compile e1))
     (λ (ρ k)
       (define a (push l ρ k))
       (c0 ρ (2opak o c1 ρ a)))]
    [_ (error 'compile "Bad ~a" e)]))

;; Store (Addr + Val) -> Set Val
(define (get-val σ v)
  (match v
    [(addr loc) (vector-ref σ loc)]
    [_ (list v)]))


(define (ap^ fun v k)
  (match fun
    [(clos l x c ρ)
     (define ρ* (bind fun v k))
     (c ρ* k)]
    [(rlos l f x c ρ)
     (define ρ* (bind fun v k))
     (c ρ* k)]
    ;; Anything else is stuck
    [_ #f]))

(define (ap-op^ o vs k)
  (match* (o vs)
    [('zero? (list (? number? n))) (yield (co^ k (zero? n)))]
    [('sub1 (list (? number? n)))  (yield (co^ k (widen (sub1 n))))]
    [('add1 (list (? number? n)))  (yield (co^ k (widen (add1 n))))]
    [('zero? (list 'number))
     (yield (co^ k #t))
     (yield (co^ k #f))]
    [('sub1 (list 'number)) (yield (co^ k 'number))]
    [('* (list (? number? n) (? number? m)))
     (yield (co^ k (widen (* m n))))]
    [('* (list (? number? n) 'number))
     (yield (co^ k 'number))]
    [('* (list 'number 'number))
     (yield (co^ k 'number))]
    ;; Anything else is stuck
    [(_ _)
     (void)]))

;; "Bytecode" interpreter
;;  State -> State^
(define (step-compiled^ s)
  (match s
    [(co^ k v)
     (match k
       ['mt (for ([v (get-val σ v)])
              (yield (ans^ v)))]
       [(ar c ρ l) (c ρ (fn v l))]
       [(fn f l)
        (for* ([k (get-cont σ l)]
               [f (get-val σ f)])
          (ap^ f v k))]
       [(ifk c a ρ l)
        (for* ([k (get-cont σ l)]
               [v (get-val σ v)])
          ((if v c a) ρ k))]

       [(1opk o l)
        (for* ([k (get-cont σ l)]
                   [v (get-val σ v)])
          (ap-op^ o (list v) k))]
       [(2opak o c ρ l)
        (c ρ (2opfk o v l))]
       [(2opfk o u l)
        (for* ([k (get-cont σ l)]
               [v (get-val σ v)]
               [u (get-val σ u)])
          (ap-op^ o (list v u) k))]
       [_ (error 'step-compiled^ "Bad ~a" k)])]

    [s s]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics
(define (widen b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (bind fun v k)
  (match fun
    [(clos l x e ρ)
     (join-many! x (get-val σ v))
     (extend ρ x x)]
    [(rlos l f x e ρ)
     (join-one! f fun)
     (join-many! x (get-val σ v))
     (extend (extend ρ x x) f f)]
    [_ (error 'bind "Bad ~a" fun)]))

(define (push l ρ k)
  (join-one! l k)
  l)

(define (join-one! a v)
  (define prev (vector-ref σ a))
  (unless (member v prev)
    (vector-set! σ a (cons v prev))
    (set! unions (add1 unions))))

(define (join-many! a vs)
  (define prev (vector-ref σ a))
  (define-values (next added?)
    (for/fold ([res prev] [added? #f])
        ([v (in-list vs)]
         #:unless (member v prev))
      (values (cons v res) #t)))
  (when added?
    (vector-set! σ a next)
    (set! unions (add1 unions))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exp -> Set Val
;; 0CFA with store widening and specialized iteration
(define (aval^ e)
  (set! todo '())
  (set! seen (make-hash))
  (define fst (inj e))
  (time ;; ignore preprocessing
   (let loop ()
     (cond [(null? todo)
            (for*/set ([(c at-unions) (in-hash seen)]
                       #:when (ans^? c))
              (ans^-v c))]
           [else
            (wide-step-specialized seen)
            (loop)]))))

;; Sexp -> Set State
(define (inj sexp)
  (define-values (e nlabels) (parse sexp))
  (set! σ (make-vector nlabels '()))
  ((compile e) #;empty-environment-> (hash) 'mt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ -> State^
;; Specialized from wide-step : State^ -> { State^ } ≈ State^ -> State^
(define (wide-step-specialized seen)
  (define todo-old todo)
  (set! todo '())
  (for ([c (in-list todo-old)]) (step-compiled^ c)))

(aval^ church)
