#lang racket
(require "notation.rkt" "tcon.rkt")
(provide (all-defined-out))

;; An Exp is one of:
;; (var Lab Exp)
;; (lam Lab Sym Exp)
;; (app Lab Exp Exp)
;; (if Lab Exp Exp Exp)
;; (st! Lab Var Exp)
;; (lcc Lab Var Exp)
;; (primr Lab Sym)
;; (datum Lab Atom)
(struct exp (lab)             #:transparent)
(struct var exp (name)        #:transparent)
(struct lrc exp (xs es e)     #:transparent)
(struct lam exp (xs exp)      #:transparent)
(struct rlm exp (xs rest exp) #:transparent)
(struct app exp (ℓchk rator rand)  #:transparent)
(struct ife exp (t c a)       #:transparent)
(struct st! exp (x e)         #:transparent)
(struct lcc exp (x e)         #:transparent)
;; Stack inspection forms
(struct grt exp (r e)         #:transparent) ;; Grant
(struct fal exp ()            #:transparent) ;; Fail
(struct frm exp (r e)         #:transparent) ;; Frame
(struct tst exp (r t e)       #:transparent) ;; Test
;; Contract monitoring forms
(struct mon exp (ℓchk pℓ nℓ sℓ s e) #:transparent) ;; Structural contract
(struct tmon exp (ℓchk pℓ nℓ sℓ s t e) #:transparent) ;; Temporal contract attached to structural contract.
;; Structural contract constructors
(struct consc exp (ca cd)     #:transparent)
(struct andc exp (c₀ c₁)      #:transparent)
(struct orc exp (c₀ c₁)       #:transparent) ;; Only rightmost may be higher-order
(struct fltc exp (e)          #:transparent)
(struct -anyc exp ()          #:transparent) (define anyc (-anyc -1))
(struct -nonec exp ()         #:transparent) (define nonec (-nonec -1))
(struct arrc exp (name ncs pc) #:transparent)
;; Note: Temporal contract constructors from tcon
;; Top level timeline
(struct -Λη ()) (define Λη (-Λη))

(struct primr exp (which)    #:transparent)
;; (dst Lab Sym List[Pair[Sym Boolean]] Exp)
;; Define struct form that should die after we go to real Racket.
(struct dst exp (name fields e) #:transparent)

;; Unmerged data.
(struct datum exp (val) #:transparent)
;; Merged versions of data that must be evaluated specially.
(struct mk-list^ exp (vals) #:transparent)
(struct mk-improper^ exp (vals last) #:transparent)
(struct mk-vector^ exp (vals) #:transparent)
(struct mk-hash^ exp (keys vals) #:transparent)

(define (free e)
  (define (expr-free e bound)
    (define (loop e) (expr-free e bound))
    (match e
      [(var _ name) (if (name . ∈ . bound) ∅ (set name))]
      [(lrc _ xs es e)
       (define bound* (∪/l bound xs))
       (for/union #:initial (expr-free e bound*)
                  ([e (in-list es)])
         (expr-free e bound*))]
      [(lam _ vars body) (expr-free body (∪/l bound vars))]
      [(rlm _ vars rest body) (expr-free body (∪1 (∪/l bound vars) rest))]
      [(app _ _ rator rands) (for/union #:initial (loop rator)
                                      ([rand (in-list rands)])
                             (loop rand))]
      [(ife _ t c a) (∪ (loop t) (loop c) (loop a))]
      [(st! _ x e)
       (define efs (loop e))
       (if (x . ∈ . bound) efs (∪1 efs x))]
      [(lcc _ x e) (expr-free e (∪1 bound x))]
      [(primr _ _) ∅]
      [(datum _ _) ∅]
      ;; Continuation mark forms
      [(grt _ _ e) (loop e)]
      [(frm _ _ e) (loop e)]
      [(fal _) ∅]
      [(tst _ _ t e) (∪ (loop t) (loop e))]
      ;; Monitoring forms
      [(or (mon _ _ _ _ _ s e)
           (tmon _ _ _ _ _ s _ e))
       (∪ (scon-free s bound) (loop e))]
      [_ (error 'free "Bad expr ~a" e)]))
  (define (scon-free s bound)
    (define (loop s) (scon-free s bound))
    (match s
      [(or (consc _ s₀ s₁)
           (orc _ s₀ s₁)
           (andc _ s₀ s₁))
       (∪ (loop s₀) (loop s₁))]
      [(fltc _ e) (expr-free e bound)]
      [(arrc _ _ ncs pc)
       (for/union #:initial (loop pc) ([nc (in-list ncs)]) (loop nc))]
      [(or (== anyc eq?) (== nonec eq?)) ∅]
      [_ (error 'scon-free "Bad scon ~a" s)]))
  (expr-free e ∅))