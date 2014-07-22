#lang racket/base
(require (for-syntax racket/base syntax/parse)
         racket/splicing racket/match racket/stxparam
         (except-in racket/set for/set for*/set)
         racket/promise
         "notation.rkt" "do.rkt" "imperative.rkt" "env.rkt" "prealloc.rkt"
         (only-in "primitives.rkt" yield-meaning))
(provide prepare-pushdown
         with-non-memoizing-pushdown with-memoizing-pushdown with-memoizing-pushdown/stacked
         with-pushdown-mutable-worklist with-pushdown-mutable-worklist/stacked
         mk-pushdown-imperative/timestamp^-fixpoint/stacked
         mk-pushdown-prealloc/timestamp^-fixpoint/stacked
         mk-pushdown-imperative/timestamp^-fixpoint
         mk-pushdown-prealloc/timestamp^-fixpoint
         with-regular

         Ξ Ξage)
(define Ξ (make-hash))
(define Ξage 0) (define (inc-Ξage!) (set! Ξage (add1 Ξage)))
(define ΞΔ? #f)
(define M (make-hash))
(define (reset-ΞΔ?!) (when ΞΔ? (inc-Ξage!) (set! ΞΔ? #f)))

;; TODO: split Ξages across ctxs for less propagation.

(mk-mk-imperative/timestamp^-fixpoint
 mk-pushdown-imperative/timestamp^-fixpoint
 restrict-to-reachable
 (void)
 Ξ)
(mk-mk-imperative/timestamp^-fixpoint
 mk-pushdown-prealloc/timestamp^-fixpoint
 restrict-to-reachable/vector
 (void)
 Ξ)

(mk-mk-imperative/timestamp^-fixpoint
 mk-pushdown-imperative/timestamp^-fixpoint/stacked
 restrict-to-reachable/stacked
 (begin (reset-ΞΔ?!) (reset-∆?!)))
(mk-mk-imperative/timestamp^-fixpoint
 mk-pushdown-prealloc/timestamp^-fixpoint/stacked
 restrict-to-reachable/vector/stacked
 (begin (reset-ΞΔ?!) (reset-∆?!)))

(define (non-memo-yield! c)
  (define seenc (hash-ref seen c #f))
  (cond
   [(and (pair? seenc)
         (= unions (car seenc))
         (= Ξage (cdr seenc)))
    (void)]
   [else
    (hash-set! seen c (cons unions Ξage))
    (add-todo! c)]))

(define (non-memo-yield/stacked! c)
  (define stack (hash-ref seen c '()))
  ;; We have seen this state before if there has been no store change and
  ;; the current timestamp is at the top of the stack.
  (define top-op (and (pair? stack) (car stack)))
  (define next-unions (if ∆? (add1 unions) unions))
  (define next-Ξage (if ΞΔ? (add1 Ξage) Ξage))
  (define (do-add)
    (hash-set! seen c (cons (cons next-unions next-Ξage) stack))
    (add-todo! c))
  (match top-op
    ;; haven't seen state before, and there was a store update.
    [#f (do-add)]
    [(cons σage* Ξage*)
     ;; Saw state previously, but there was a store or Ξ update. 
     (if (or (if ∆? (>= unions σage*) (> unions σage*))
             (if ΞΔ? (>= Ξage Ξage*) (> Ξage Ξage*)))
         (do-add)
         (void))]))
(define-for-syntax ¬memo-yield! (syntax-rules () [(_ e) (non-memo-yield! e)]))
(define-for-syntax ¬memo-yield/stacked! (syntax-rules () [(_ e) (non-memo-yield/stacked! e)]))

(define (add-ctx/stacked! c k)
  (match (hash-ref Ξ c -unmapped)
    [(== -unmapped eq?)
     (set! ΞΔ? #t)
     (hash-set! Ξ c (set k))]
    [S (unless (set-member? S k)
         (set! ΞΔ? #t)
         (hash-set! Ξ c (set-add S k)))]))

(define (add-ctx! c k)
  (match (hash-ref Ξ c -unmapped)
    [(== -unmapped eq?)
     (inc-Ξage!)
     (hash-set! Ξ c (set k))]
    [S (unless (set-member? S k)
         (inc-Ξage!)
         (hash-set! Ξ c (set-add S k)))]))

(define (add-result! c res) (hash-add! M c res))
(define (prepare-pushdown)
  (hash-clear! Ξ)
  (set! Ξage 0)
  (set! ΞΔ? #f)
  (hash-clear! M))

(struct unmapped ()) (define -unmapped (unmapped))
(define (popfail k) (error 'pop "Bad continuation ~a" k))
(define-simple-macro* (popaux k ctx? [mtpat . mtrhs] [φpat . φrhs] (~optional to-memoize))
  (let ([G (mutable-seteq)]
        #,@(listy (and (attribute to-memoize) #'[Mv to-memoize])))
    (do (target-σ) loop ([kid k])
        (match kid
          [mtpat . mtrhs]
          [φpat . φrhs]
          [(? ctx?)
           (if (set-member? G kid)
               (continue)
               (begin (set-add! G kid)
                      #,@(listy (and (attribute to-memoize) #'(add-result! kid Mv)))
                      (do (target-σ) ([k* (in-set (hash-ref Ξ kid))])
                        (loop target-σ k*))))]
          [_ (popfail kid)]))))

(define-syntax (regular-do-pop stx)
  (syntax-parse stx
    [(_ _ (_ k:expr) mt-clause φ-clause)
     #`(do (target-σ) ([k* #:in-force target-σ k])
         (match k*
           mt-clause
           φ-clause
           [_ (popfail k*)]))]))

(define-syntax-rule (regular-bind-push (σ* a* bpσ l δ k) body)
  (let ([a* (make-var-contour l δ)])
    (bind-force (res-tmp bpσ k)
                (bind-join (σ* bpσ a* res-tmp) body))))

(define-syntax-rule (pushdown-bind-push (σ* a* bpσ l δ k) body)
  (let ([a* k]) body))

(define-syntax (memoizing-do-pop stx)
  (syntax-parse stx
    [(_ ctx? (to-memo:expr k:expr) mt-clause φ-clause)
     #'(popaux k ctx? mt-clause φ-clause to-memo)]))

(define-syntax (non-memoizing-do-pop stx)
  (syntax-parse stx
    [(_ ctx? (_ k:expr) mt-clause φ-clause)
     #'(popaux k ctx? mt-clause φ-clause)]))

(define-syntax (bind-memo-do-nothing stx)
  (syntax-parse stx
    [(_ (r:id ctx:expr) (~or (~once with-results:expr) (~once (~seq #:unmapped unm:expr))) ...)
     #'unm]))

(define-syntax (bind-ctx-do-nothing stx)
  (syntax-parse stx
    [(_ (k:id ctx:expr kont:expr) . body)
     #'(let ([k kont]) . body)]))

(define-syntax (bind-memo-lookup stx)
  (syntax-parse stx
    [(_ (r:id ctx:expr) (~or (~once with-results:expr) (~once (~seq #:unmapped unm:expr))) ...)
     #'(match (hash-ref M ctx -unmapped)
         [(== -unmapped eq?) unm]
         [r with-results])]))

(define-syntax (bind-ctx-bang stx)
  (syntax-parse stx
    [(_ (k:id ctx:expr kont:expr) . body)
     #'(let ([k ctx]
             [kv kont])
         (add-ctx! k kv)
         . body)]))

(define-syntax (bind-ctx/stacked stx)
  (syntax-parse stx
    [(_ (k:id ctx:expr kont:expr) . body)
     #'(let ([k ctx]
             [kv kont])
         (add-ctx/stacked! k kv)
         . body)]))

(define-syntax-rule (bind-no-delay-kont (res σ a) . body)
  (let ([res a]) . body))

(define-syntax-rule (in-delay (res σ a) . body)
  (bind-delay (res-tmp σ a) (do (σ) ([res (in-set res-tmp)]) . body)))
(define-syntax-rule (in-non-delayed (res σ a) . body)
  (let ([res a]) . body))

(define-syntax-rule (with-regular . body)
  (splicing-syntax-parameterize
   ([bind-memo (make-rename-transformer #'bind-memo-do-nothing)]
    [bind-ctx (make-rename-transformer #'bind-ctx-do-nothing)]
    [bind-push (make-rename-transformer #'regular-bind-push)]
    [in-delay-kont (make-rename-transformer #'in-delay)]
    [do-pop (make-rename-transformer #'regular-do-pop)])
   . body))

(define-syntax-rule (pushdown-base . body)
  (splicing-syntax-parameterize
   ([bind-push (make-rename-transformer #'pushdown-bind-push)]
    [in-delay-kont (make-rename-transformer #'in-non-delayed)])
   . body))

(define-syntax-rule (with-memoizing-pushdown . body)
  (splicing-syntax-parameterize
   ([bind-memo (make-rename-transformer #'bind-memo-lookup)]
    [do-pop (make-rename-transformer #'memoizing-do-pop)]
    [bind-ctx (make-rename-transformer #'bind-ctx)])
   (pushdown-base . body)))

(define-syntax-rule (with-memoizing-pushdown/stacked . body)
  (splicing-syntax-parameterize
   ([bind-memo (make-rename-transformer #'bind-memo-lookup)]
    [do-pop (make-rename-transformer #'memoizing-do-pop)]
    [bind-ctx (make-rename-transformer #'bind-ctx/stacked)])
   (pushdown-base . body)))

(define-syntax-rule (with-non-memoizing-pushdown . body)
  (splicing-syntax-parameterize
   ([bind-memo (make-rename-transformer #'bind-memo-do-nothing)]
    [do-pop (make-rename-transformer #'non-memoizing-do-pop)])
   (pushdown-base . body)))

(define-syntax-rule (with-pushdown-mutable-worklist . body)
  (splicing-syntax-parameterize ([yield-meaning ¬memo-yield!]
                                 [bind-ctx (make-rename-transformer #'bind-ctx-bang)]) . body))
(define-syntax-rule (with-pushdown-mutable-worklist/stacked . body)
  (splicing-syntax-parameterize ([yield-meaning ¬memo-yield/stacked!]
                                 [bind-ctx (make-rename-transformer #'bind-ctx/stacked)]) . body))
