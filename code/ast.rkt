#lang racket
(require "notation.rkt")
(provide (all-defined-out))

;; An Exp is one of:
;; (var Lab Exp)
;; (lam Lab Sym Exp)
;; (app Lab Exp Exp)
;; (if Lab Exp Exp Exp)
;; (primr Lab Sym)
;; (datum Lab Atom)
(struct exp (lab)             #:transparent)
(struct var exp (name)        #:transparent)
(struct lrc exp (xs es e)     #:transparent)
(struct lam exp (xs exp)      #:transparent)
(struct rlm exp (xs rest exp) #:transparent)
(struct app exp (rator rand)  #:transparent)
(struct ife exp (t c a)       #:transparent)
(struct st! exp (x e)         #:transparent)

(struct primr exp (which)    #:transparent)

;; Unmerged data.
(struct datum exp (val) #:transparent)
;; Merged versions of data.
(struct list^ exp (val) #:transparent)
(struct improper^ exp (val last) #:transparent)
(struct vector^ exp (val) #:transparent)
(struct hash^ exp (val) #:transparent)

(define (free e)
  (let loop* ([e e]
              [bound (set)])
    (define (loop e) (loop* e bound))
    (match e
      [(var _ name) (if (name . ∈ . bound) ∅ (set name))]
      [(lrc _ xs es e)
       (define bound* (∪/l bound xs))
       (for/union #:initial (loop* e bound*)
                  ([e (in-list es)])
         (loop* e bound*))]
      [(lam _ vars body) (loop* body (∪/l bound vars))]
      [(rlm _ vars rest body) (loop* body (∪1 (∪/l bound vars) rest))]
      [(app _ rator rands) (for/union #:initial (loop rator)
                                      ([rand (in-list rands)])
                             (loop rand))]
      [(ife _ t c a) (∪ (loop t) (loop c) (loop a))]
      [(st! _ x e)
       (define efs (loop e))
       (if (x . ∈ . bound) efs (∪1 efs x))]
      [(primr _ _) ∅]
      [(datum _ _) ∅]
      [_ (error 'free "Bad expr ~a" e)])))