#lang racket
(require "notation.rkt" (for-syntax syntax/parse racket/list) racket/generic
         racket/trace)
(provide (all-defined-out))

(struct exp (lab fvs-box) #:transparent)

(struct opaque-box ([v #:mutable]))
(define-generics binds-variables
  [free-box binds-variables]
  [free binds-variables]
  #:fallbacks [(define (free e) ∅)
               (define free-box exp-fvs-box)])
(define (trace-free!) (trace free))
(define (untrace-free!) (untrace free))

(define-simple-macro* (def-free free
                        (~or (~optional (~seq #:gfree gfree) #:defaults ([gfree #'gfree]))
                             (~optional (~seq #:wcs wcs:exact-nonnegative-integer) #:defaults ([wcs #'1]))) ...
                        [(struct pats ...) rhss ...])
  (begin 
    (define/generic gfree free)
    (define (free e)
      (or (opaque-box-v (free-box e))
          (let ()
            (match e [(struct #,@(make-list (syntax-e #'wcs) #'_) fvs-box pats ...)
                      (define fvs (let () rhss ...))
                      (set-opaque-box-v! fvs-box fvs)
                      fvs]))))))

;; An Exp is one of:
;; (var Lab Exp)
;; (lam Lab Sym Exp)
;; (app Lab Exp Exp)
;; (if Lab Exp Exp Exp)
;; (st! Lab Var Exp)
;; (lcc Lab Var Exp)
;; (primr Lab Sym)
;; (datum Lab Atom)
(define-simple-macro* (exp-struct name (fields ...) [methods ...])
  (struct name exp (fields ...) #:transparent
          #:methods #,(syntax-local-introduce #'gen:binds-variables) [methods ...]))
(exp-struct var (name)
        [(def-free free [(var x) (set x)])])
(exp-struct lrc (xs es e)
            [(def-free free #:gfree gfree
              [(lrc xs es e)
               ((∪ ((union-map gfree) es) (gfree e)) . ∖/l . xs)])])
(exp-struct lam (xs exp)
        [(def-free free #:gfree gfree [(lam xs e) ((gfree e) . ∖/l . xs)])])
(exp-struct rlm (xs rest exp)
        [(def-free free #:gfree gfree
           [(rlm xs rest e) ((gfree e) . ∖/l . (cons rest xs))])])
(exp-struct app (ℓchk rator rand)
        [(def-free free #:gfree gfree [(app _ e0 es) (∪ (gfree e0) ((union-map gfree) es))])])
(exp-struct ife (t c a)
        [(def-free free #:gfree gfree [(ife g t e) (∪ (gfree g) (gfree t) (gfree e))])])
(exp-struct st! (x e)
        [(def-free free #:gfree gfree
           [(st! x e) (∪1 (gfree e) x)])])
(exp-struct lcc (x e)
        [(def-free free #:gfree gfree [(lcc x e) ((gfree e) . ∖1 . x)])])
;; Stack inspection forms
(exp-struct grt (r e)
        [(def-free free #:gfree gfree [(grt _ e) (gfree e)])])
(exp-struct fal () [])
(exp-struct frm (r e)
        [(def-free free #:gfree gfree [(frm _ e) (gfree e)])])
(exp-struct tst (r t e)
        [(def-free free #:gfree gfree [(tst _ t e) (∪ (gfree t) (gfree e))])])
;; Contract monitoring forms
(exp-struct mon (ℓchk pℓ nℓ sℓ s e)
        [(def-free free #:gfree gfree [(mon _ _ _ _ s e) (∪ (gfree s) (gfree e))])])
(exp-struct tmon (ℓchk pℓ nℓ sℓ s t e)
        [(def-free free #:gfree gfree [(tmon _ _ _ _ s t e) (∪ (gfree s) (gfree t) (gfree e))])])
;; Structural contract constructors
(exp-struct consc (ca cd)
        [(def-free free #:gfree gfree [(consc ca cd) (∪ (gfree ca) (gfree cd))])])
(exp-struct andc (c₀ c₁)
        [(def-free free #:gfree gfree [(andc c₀ c₁)  (∪ (gfree c₀) (gfree c₁))])])
(exp-struct orc (c₀ c₁)
        [(def-free free #:gfree gfree [(orc c₀ c₁)  (∪ (gfree c₀) (gfree c₁))])])
(exp-struct fltc (e)
        [(def-free free #:gfree gfree [(fltc e) (gfree e)])])
(exp-struct arrc (name ncs pc)
            [(def-free free #:gfree gfree [(arrc _ ncs pc) (∪ ((union-map gfree) ncs) (gfree pc))])])
(struct -anyc () #:methods gen:binds-variables [])
(struct -nonec () #:methods gen:binds-variables [])
(define anyc (-anyc))
(define nonec (-nonec))

;; Note: Temporal contract constructors from tcon
;; Top level timeline
(struct -Λη ()) (define Λη (-Λη))

(exp-struct primr (which) [])
;; (dst Lab Sym List[Pair[Sym Boolean]] Exp)
;; Define struct form that should die after we go to real Racket.
(exp-struct dst (name fields e) [])

;; Unmerged data.
(exp-struct datum (val) [])

