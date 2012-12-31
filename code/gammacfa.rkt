#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "parameters.rkt" "context.rkt" "add-lib.rkt" "fix.rkt"
         "data.rkt" "store-passing.rkt")
(provide with-ΓCFA)

;; 0CFA
(define-syntax-rule (∪ρ (e ρ-exp) others ...) (∪ (ast-fv e) others ...))
#;(define-syntax-rule (∪ρ (e ρ-exp) others ...)
  (∪ (for/set ([(_ a) (in-set ρ-exp)]) a) others ...))

(define-for-syntax (ΓCFA-yield ev co ap ∪ρ)
  (define yield-tr (syntax-parameter-value #'yield))
  (λ (stx)
     (syntax-case stx (ev co ap)
       [(_ (ev σ e ρ k δ))
        (yield-tr #`(yield (#%app #,ev (restrict-to-set σ (#,∪ρ (e ρ) (touches k))) e ρ k δ)))]
       [(_ (co σ k v))
        (yield-tr #`(yield (#%app #,co (restrict-to-set σ (∪ (touches k) (touches v))) k v)))]
       [(_ (ap σ l fn-addr arg-addrs k δ))
        (yield-tr #`(yield (#%app #,ap
                            (restrict-to-set σ (∪1 (∪/l (touches k) arg-addrs) fn-addr))
                            l fn-addr arg-addrs k δ)))]
       [(_ e) (yield-tr #`(yield e))])))

(define-for-syntax ((mk-ΓCFA ev co ap ast-fv) stx)
  (syntax-case stx ()
    [(_ () . body)
     #`(splicing-let-syntax ([∪ρ (syntax-rules ()
                                   [(_ (e ρ) others (... ...))
                                    (∪ (#%app #,ast-fv e) others (... ...))])])
         (splicing-syntax-parameterize ([yield (ΓCFA-yield #'#,ev #'#,co #'#,ap #'∪ρ)])
           . body))]))

(define-syntax-rule (with-ΓCFA (mk-analysis) body ...)
  (splicing-let-syntax
   ([mk-analysis
     (syntax-rules ()
       [(_ . args)
        (splicing-syntax-parameterize ([in-scope-of-extras (mk-ΓCFA #'ev #'co #'ap #'ast-fv)])
          (mk-analysis #:ev ev #:co co #:ap ap #:ast ast . args))])])
   body ...))
