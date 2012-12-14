#lang racket
(require "notation.rkt")
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
;; Forms are mutable for in-place transformations.
(struct exp (lab tail?)       #:transparent)
(struct var exp (name)        #:transparent)
(struct lrc exp (xs es e)     #:transparent #:mutable) ;; letrec
(struct lte exp (xs es e)     #:transparent #:mutable) ;; let
(struct lam exp (xs exp)      #:transparent #:mutable)
(struct rlm exp (xs rest exp) #:transparent #:mutable)
(struct app exp (rator rand)  #:transparent #:mutable)
(struct ife exp (t c a)       #:transparent #:mutable)
(struct st! exp (x e)         #:transparent #:mutable)
(struct lcc exp (x e)         #:transparent #:mutable)
(struct pfl exp (fallback e)  #:transparent) ;; Primitive apply fallback value
;; Stack inspection forms
(struct grt exp (r e)         #:transparent) ;; Grant
(struct fal exp ()            #:transparent) ;; Fail
(struct frm exp (r e)         #:transparent) ;; Frame
(struct tst exp (r t e)       #:transparent) ;; Test

(struct primr exp (which fallback) #:transparent)
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
  (let loop* ([e e]
              [bound (set)])
    (define (loop e) (loop* e bound))
    (match e
      [(var _ _ name) (if (name . ∈ . bound) ∅ (set name))]
      [(lrc _ _ xs es e)
       (define bound* (∪/l bound xs))
       (for/union #:initial (loop* e bound*)
                  ([e (in-list es)])
         (loop* e bound*))]
      [(lte _ _ xs es e)
       (define bound* (∪/l bound xs))
       (for/union #:initial (loop* e bound*)
                  ([e (in-list es)])
         (loop* e bound))]
      [(lam _ _ vars body) (loop* body (∪/l bound vars))]
      [(rlm _ _ vars rest body) (loop* body (∪1 (∪/l bound vars) rest))]
      [(app _ _ rator rands) (for/union #:initial (loop rator)
                                      ([rand (in-list rands)])
                             (loop rand))]
      [(ife _ _ t c a) (∪ (loop t) (loop c) (loop a))]
      [(st! _ _ x e)
       (define efs (loop e))
       (if (x . ∈ . bound) efs (∪1 efs x))]
      [(lcc _ _ x e) (loop* e (∪1 bound x))]
      [(primr _ _ _ _) ∅]
      [(datum _ _ _) ∅]
      [(pfl _ _ _ e) (loop e)]
      ;; Continuation mark forms
      [(grt _ _ _ e) (loop e)]
      [(frm _ _ _ e) (loop e)]
      [(fal _ _) ∅]
      [(tst _ _ _ t e) (∪ (loop t) (loop e))]
      [_ (error 'free "Bad expr ~a" e)])))