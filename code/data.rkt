#lang racket
(require "ast.rkt")
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
;; - (clos Sym Exp Env)
;; - (primop Sym)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (vectorv Number Addr) ;; collapsed into one addr
(struct clos (x e ρ)   #:transparent)
(struct primop (which) #:transparent)
(struct consv (car cdr) #:transparent)
(struct vectorv^ (length cell) #:transparent)
(struct vectorv (length cells) #:transparent)

;; What are the supported primitives for a datum form?
;; REMARK: no list literals.
(define (atomic? x)
  (or (number? x)
      (boolean? x)
      (void? x)
      (string? x)
      (symbol? x)
      (null? x)))

(define (touches v [0cfa? #f])
  (match v
    [(clos xs e ρ)
     (cond [0cfa? (free e)]
           [else
            (for/hash ([x (in-set (free e))]
                       #:unless (memv x xs))
              (hash-ref ρ x
                        (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ))))])]
    [(consv a d) (set a d)]
    [(vectorv _ l) (list->set l)]
    [(vectorv^ _ a) (set a)]
    [_ (set)]))

;; A Cont is one of:
;; - 'mt
;; - (ifk Exp Exp Env Cont)
;; - (lrk Sym [Listof Sym] [Listof Exp] Exp Env Cont)
;; - (sk! Sym Cont)
;; - (ls [Listof Exp] [Listof Val] Env Cont)
(struct mt ()                 #:transparent)
(struct ifk (c a ρ k δ)       #:transparent)
(struct lrk (x xs es e ρ k δ) #:transparent)
(struct sk! (x k)             #:transparent)
(struct ls (l es vs ρ k δ)    #:transparent)

(struct addr (a) #:transparent)
