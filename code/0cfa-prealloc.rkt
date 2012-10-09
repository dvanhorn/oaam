#lang racket
(provide aval^ widen)
(require "old-ast.rkt"
         (except-in "old-data.rkt" get-cont)
         "old-progs.rkt"
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
(define nlabels #f)

(define (get-cont σ l)
  (vector-ref σ l))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Compiled" Machine

;; Compile away interpretive overhead of "ev" states

;; Expr -> Comp
(define (compile e)
  (match e
    [(var l x)
     (λ (ρ k)
       (set (co^ k (addr (lookup-env ρ x)))))]
    [(num l n)   (λ (ρ k) (set (co^ k n)))]
    [(bln l b)   (λ (ρ k) (set (co^ k b)))]
    [(lam l x e)
     (define c (compile e))
     (λ (ρ k) (set (co^ k (clos l x c ρ))))]
    [(rec f (lam l x e))
     (define c (compile e))
     (λ (ρ k) (set (co^ k (rlos l f x c ρ))))]
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

;; "Bytecode" interpreter
;;  State -> State^
(define (step-compiled^ s)
  (match s
    [(co^ k v)
     (match k
       ['mt (for*/set ([v (get-val σ v)])
              (ans^ v))]
       [(ar c ρ l) (c ρ (fn v l))]
       [(fn f l)
        (for*/set ([k (get-cont σ l)]
                    [f (get-val σ f)])
          (ap^ f v k))]
       [(ifk c a ρ l)
        (for*/union ([k (get-cont σ l)]
                     [v (get-val σ v)])
          ((if v c a) ρ k))]

       [(1opk o l)
        (for*/set ([k (get-cont σ l)]
                    [v (get-val σ v)])
          (ap-op^ o (list v) k))]
       [(2opak o c ρ l)
        (c ρ (2opfk o v l))]
       [(2opfk o u l)
        (for*/set ([k (get-cont σ l)]
                    [v (get-val σ v)]
                    [u (get-val σ u)])
          (ap-op^ o (list v u) k))]
       [_ (error 'step-compiled^ "Bad ~a" k)])]

    [(ap^ fun a k)
     (match fun
       [(clos l x c ρ)
        (define ρ* (bind s))
        (c ρ* k)]
       [(rlos l f x c ρ)
        (define ρ* (bind s))
        (c ρ* k)]
       ;; Anything else is stuck
       [_ (set s)])]

    [(ap-op^ o vs k)
     (match* (o vs)
       [('zero? (list (? number? n))) (set (co^ k (zero? n)))]
       [('sub1 (list (? number? n)))  (set (co^ k (widen (sub1 n))))]
       [('add1 (list (? number? n)))  (set (co^ k (widen (add1 n))))]
       [('zero? (list 'number))
        (set (co^ k #t)
             (co^ k #f))]
       [('sub1 (list 'number)) (set (co^ k 'number))]
       [('* (list (? number? n) (? number? m)))
        (set (co^ k (widen (* m n))))]
       [('* (list (? number? n) 'number))
        (set (co^ k 'number))]
       [('* (list 'number 'number))
        (set (co^ k 'number))]
       ;; Anything else is stuck
       [(_ _)
        (set s)])]

    [s (set s)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics
(define (widen b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (bind s)
  (match s
    [(ap^ (clos l x e ρ) v k)
     (join-many! x (get-val σ v))
     (extend ρ x x)]
    [(ap^ (rlos l f x e ρ) v k)
     (join-one! f (rlos l f x e ρ))
     (join-many! x (get-val σ v))
     (extend (extend ρ x x) f f)]
    [_ (error 'bind "Bad ~a" s)]))

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
  (define fst (inj e))
  (define seen (make-hash (for/list ([c (in-set fst)])
                            (cons c unions))))
  (time ;; ignore preprocessing
   (let loop ([todo fst])
     (cond [(set-empty? todo)
            (for*/set ([(c at-unions) (in-hash seen)]
                       #:when (ans^? c))
              (ans^-v c))]
           [else
            (loop (wide-step-specialized todo seen))]))))

;; Sexp -> Set State
(define (inj sexp)
  (define nlabels 0)
  (define e (parse sexp (λ (n) (set! nlabels n))))
  (set! σ (make-vector nlabels '()))
  ((compile e) #;empty-environment-> (hash) 'mt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ -> State^
;; Specialized from wide-step : State^ -> { State^ } ≈ State^ -> State^
(define (wide-step-specialized cs seen)
  (for*/fold ([cs* (set)])
      ([c (in-set cs)]
       [s (in-set (step-compiled^ c))]
       #:unless (= unions (hash-ref seen s -1)))
    (when (set? s) (error 'wide-step-specialized "Bad step ~a" c))
    (hash-set! seen s unions)
    (set-add cs* s)))

(aval^ church)