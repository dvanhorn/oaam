#lang racket
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
(struct vectorv (length cells) #:transparent)

(struct stuck* () #:transparent)
(define stuck (stuck*))

;; A Cont is one of:
;; - 'mt
;; - (ifk Exp Exp Env Cont)
;; - (lrk Sym [Listof Sym] [Listof Exp] Exp Env Cont)
;; - (sk! Sym Cont)
;; - (ls [Listof Exp] [Listof Val] Env Cont)
(struct mt () #:transparent)
(struct ifk (c a ρ k)       #:transparent)
(struct lrk (x xs es e ρ k) #:transparent)
(struct sk! (x k)           #:transparent)
(struct ls (es vs ρ k)      #:transparent)

;; State
(struct state (σ)            #:transparent)
(struct ev state (e ρ k δ)   #:transparent)
(struct co state (k v)       #:transparent)
(struct ap state (f a k l)   #:transparent)
(struct ap-op state (o vs k) #:transparent)
(struct ans state (v)        #:transparent)

(struct addr (a) #:transparent)

;; Conf
(struct ev^ (e ρ k δ)   #:transparent)
(struct co^ (k v)       #:transparent)
(struct ap^ (f a k)     #:transparent)
(struct ap-op^ (o vs k) #:transparent)
(struct ans^ (v)        #:transparent)

;; Conf Store -> State
(define (c->s c σ)
  (match c
    [(ev^ e ρ k δ)   (ev σ e ρ k δ)]
    [(co^ k v)       (co σ k v)]
    [(ap^ f a k)     (ap σ f a k)]
    [(ap-op^ o vs k) (ap-op σ o vs k)]
    [(ans^ v)        (ans σ v)]))

;; State -> Conf
(define (s->c s)
  (match s
    [(ev _ e ρ k δ)   (ev^ e ρ k δ)]
    [(co _ k v)       (co^ k v)]
    [(ap _ f a k l)   (ap^ f a k l)]
    [(ap-op _ o vs k) (ap-op^ o vs k)]
    [(ans _ v)        (ans^ v)]))
