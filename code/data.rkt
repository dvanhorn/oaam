#lang racket
(provide (all-defined-out))

;; A Val is one of:
;; - Number
;; - Boolean
;; - Void
;; - (clos Lab Sym Exp Env)
;; - (rlos Lab Sym Sym Exp Env)
(struct clos (l x e ρ)   #:transparent)
(struct rlos (l f x e ρ) #:transparent)

;; A Cont is one of:
;; - 'mt
;; - (ifk Exp Exp Env Cont)
;; - (1opk Opr Cont)
;; - (2opak Opr Exp Env Cont)
;; - (2opfk Opr Val Cont)
;; - (lrk Sym [Listof Sym] [Listof Exp] Exp Env Cont)
;; - (sk! Sym Cont)
;; - (ls [Listof Exp] [Listof Val] Env Cont)
(struct ifk (c a ρ k)       #:transparent)
(struct 1opk (o k)          #:transparent)
(struct 2opak (o e ρ k)     #:transparent)
(struct 2opfk (o v k)       #:transparent)
(struct lrk (x xs es e ρ k) #:transparent)
(struct sk! (x k)           #:transparent)
(struct ls (es vs ρ k)      #:transparent)

;; State
(struct state (σ)            #:transparent)
(struct ev state (e ρ k)     #:transparent)
(struct co state (k v)       #:transparent)
(struct ap state (f a k)     #:transparent)
(struct ap-op state (o vs k) #:transparent)
(struct ans state (v)        #:transparent)

(struct addr (a) #:transparent)

;; Conf
(struct ev^ (e ρ k)     #:transparent)
(struct co^ (k v)       #:transparent)
(struct ap^ (f a k)     #:transparent)
(struct ap-op^ (o vs k) #:transparent)
(struct ans^ (v)        #:transparent)

;; Conf Store -> State
(define (c->s c σ)
  (match c
    [(ev^ e ρ k) (ev σ e ρ k)]
    [(co^ k v)   (co σ k v)]
    [(ap^ f a k) (ap σ f a k)]
    [(ap-op^ o vs k) (ap-op σ o vs k)]
    [(ans^ v) (ans σ v)]))

;; State -> Conf
(define (s->c s)
  (match s
    [(ev _ e ρ k) (ev^ e ρ k)]
    [(co _ k v)   (co^ k v)]
    [(ap _ f a k) (ap^ f a k)]
    [(ap-op _ o vs k) (ap-op^ o vs k)]
    [(ans _ v) (ans^ v)]))


