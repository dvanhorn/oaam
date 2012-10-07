#lang racket
(provide (all-defined-out))

;; A Val is one of:
;; - Number
;; - Boolean
;; - (clos Lab Sym Exp Env)
;; - (rlos Lab Sym Sym Exp Env)
(struct clos (l x e ρ)   #:transparent)
(struct rlos (l f x e ρ) #:transparent)

;; A Cont is one of:
;; - 'mt
;; - (ar Exp Env Cont)
;; - (fn Val Cont)
;; - (ifk Exp Exp Env Cont)
;; - (1opk Opr Cont)
;; - (2opak Opr Exp Env Cont)
;; - (2opfk Opr Val Cont)
(struct ar (e ρ k)      #:transparent)
(struct fn (v k)        #:transparent)
(struct ifk (c a ρ k)   #:transparent)
(struct 1opk (o k)      #:transparent)
(struct 2opak (o e ρ k) #:transparent)
(struct 2opfk (o v k)   #:transparent)

;; State
(struct state (σ)            #:transparent)
(struct ev state (e ρ k)     #:transparent)
(struct co state (k v)       #:transparent)
(struct ap state (f a k)     #:transparent)
(struct ap-op state (o vs k) #:transparent)
(struct ans state (v)        #:transparent)

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

(define (lookup ρ σ x)
  (hash-ref σ (hash-ref ρ x)))
(define (lookup-env ρ x)
  (hash-ref ρ x))
(define (get-cont σ l)
  (hash-ref σ l))
(define (extend ρ x v)
  (hash-set ρ x v))
(define (join σ a s)
  (hash-set σ a
            (set-union s (hash-ref σ a (set)))))
(define (join-one σ a x)
  (hash-set σ a
            (set-add (hash-ref σ a (set)) x)))
