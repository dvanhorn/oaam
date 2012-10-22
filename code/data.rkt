#lang racket
(require "ast.rkt" "notation.rkt" (for-syntax syntax/parse))
(provide (all-defined-out))
;; A Val is one of:
;; - Number
;; - Boolean
;; - Void
;; - String
;; - Symbol
;; - '()
;; - 'number
;; - 'string
;; - 'symbol
;; - (primop Sym)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (vectorv Number Addr) ;; collapsed into one addr
;; - (clos List[Var] Exp Env) ;; or without Env. Constructed by mk-analysis.
(struct primop (which) #:prefab)
(struct consv (car cdr) #:prefab)
(struct vectorv^ (length cell) #:prefab)
(struct vectorv (length cells) #:prefab)

;; What are the supported primitives for a datum form?
;; REMARK: no list literals.
(define (atomic? x)
  (or (number? x)
      (boolean? x)
      (void? x)
      (string? x)
      (symbol? x)
      (null? x)))

(define-simple-macro* (mk-touches touches:id clos:id 0cfa?:boolean)
  (define (touches v)
    (match v
      [(clos xs e ρ fvs)
       #,(if (syntax-e #'0cfa?)
             #'fvs
             #'(for/hash ([x (in-set fvs)]
                          #:unless (memv x xs))
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [(consv a d) (set a d)]
      [(vectorv _ l) (list->set l)]
      [(vectorv^ _ a) (set a)]
      [(? set? s) (for/union ([v (in-set s)]) (touches v))]
      [_ (set)])))

;; A Cont is one of:
;; - 'mt
;; - (ifk Exp Exp Env Cont)
;; - (lrk Sym [Listof Sym] [Listof Exp] Exp Env Cont)
;; - (sk! Sym Cont)
;; - (ls [Listof Exp] Natural [Listof Val] Env Cont)
(struct mt ()                 #:prefab)
(struct ifk (c a ρ k δ)       #:prefab)
(struct lrk (x xs es e ρ k δ) #:prefab)
(struct sk! (x k)             #:prefab)
;; n = Which subexpression are we evaluating?
(struct ls (l n es vs ρ k δ)  #:prefab)

(struct addr (a) #:prefab)
