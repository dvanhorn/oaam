#lang racket

(require (for-syntax syntax/parse))
(provide (all-defined-out))

;; Beefy define-syntax-rule that allows syntax classes and unquote-syntax
(define-syntax (define-syntax-rule* stx)
  (syntax-parse stx
    [(_ (name patterns ...) body ...)
     (syntax-arm
      (syntax/loc stx
        (define-syntax (name syn)
          (syntax-parse syn
            [(_ patterns ...)
             (syntax-arm (quasisyntax/loc syn (begin body ...)))]))))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for/union

(begin-for-syntax
(define-splicing-syntax-class (ops initial)
  #:attributes (init res)
  (pattern (~seq (~or (~optional (~seq #:initial init:expr)
                                 #:defaults ([init initial]))
                      (~optional (~seq #:res res:id)
                                 #:defaults ([res #'acc]))) ...))))

(define-syntax-rule* (for/append (~var o (ops #''())) guards body ...+)
  (for/fold ([o.res o.init]) guards (append (let () body ...) o.res)))

;; Set notations
(define-values (∅ ∪ ∩ ∖ ∪1 ∪/l ∖1 ∖/l ∈)
  (let ([set-add*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-add s x)))]
        [set-remove*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-remove s x)))]
        [in? (λ (x s) (set-member? s x))])
    (values (set) set-union set-intersect set-subtract
            set-add set-add*
            set-remove set-remove* in?)))

(define-syntax-rule* (for/union (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-syntax-rule* (for*/union (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-syntax-rule* (for/set (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))
(define-syntax-rule* (for*/set (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))