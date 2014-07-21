#lang racket/base
(require (for-syntax racket/base syntax/parse)
         racket/splicing racket/match racket/stxparam
         (except-in racket/set for/set for*/set)
         racket/promise
         "notation.rkt" "do.rkt")
(provide prepare-pushdown with-non-memoizing-pushdown with-memoizing-pushdown with-regular)
(define Ξ (make-hash))
(define M (make-hash))

(define (add-ctx! c k) (hash-add! Ξ c k))
(define (add-result! c res) (hash-add! M c res))
(define (prepare-pushdown)
  (hash-clear! Ξ)
  (hash-clear! M))

(struct unmapped ()) (define -unmapped (unmapped))
(define (popfail k) (error 'pop "Bad continuation ~a" k))
(define-simple-macro* (popaux k ctx? mt-clause φ-clause (~optional to-memoize))
  (let ([G (mutable-seteq)]
        #,@(listy (and (attribute to-memoize) #'[Mv to-memoize])))
    (do (target-σ) loop ([kid k])
        (match kid
          mt-clause
          φ-clause
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

(define-syntax-rule (with-memoizing-pushdown . body)
  (splicing-syntax-parameterize
   ([bind-memo (make-rename-transformer #'bind-memo-lookup)]
    [do-pop (make-rename-transformer #'memoizing-do-pop)]

    [bind-ctx (make-rename-transformer #'bind-ctx-bang)]
    [bind-push (make-rename-transformer #'pushdown-bind-push)]
    [in-delay-kont (make-rename-transformer #'in-non-delayed)])
   . body))

(define-syntax-rule (with-non-memoizing-pushdown . body)
  (splicing-syntax-parameterize
   ([bind-memo (make-rename-transformer #'bind-memo-do-nothing)]
    [do-pop (make-rename-transformer #'non-memoizing-do-pop)]

    [bind-ctx (make-rename-transformer #'bind-ctx-bang)]
    [bind-push (make-rename-transformer #'pushdown-bind-push)]
    [in-delay-kont (make-rename-transformer #'in-non-delayed)])
   . body))
