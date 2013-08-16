#lang racket
(require "notation.rkt" (for-syntax syntax/parse racket/list) racket/generic)
(provide (all-defined-out))

(struct exp (lab fvs-box) #:transparent)

(define-generics binds-variables
  [free-box binds-variables]
  [free binds-variables #:bound [bound]]
  #:fallbacks [(define (free e #:bound [bound ∅]) ∅)
               (define free-box exp-fvs-box)])

(define-simple-macro* (def-free e free
                        (~or (~optional (~seq #:gfree gfree) #:defaults ([gfree #'gfree]))
                             (~optional (~seq #:self free*))
                             (~optional (~seq #:bound bound) #:defaults ([bound #'bound]))
                             (~optional (~seq #:wcs wcs:exact-nonnegative-integer) #:defaults ([wcs #'1]))) ...
                        [(struct pats ...) rhss ...])
  (begin 
    (define/generic gfree free)
    (define (free e #:bound [bound ∅])
      (or (unbox (free-box e))
          (let ()
            #,@(if (attribute free*) #'((define (free* e) (gfree e #:bound bound))) #'())
            (match e [(struct #,@(make-list (syntax-e #'wcs) #'_) fvs-box pats ...)
                      (define fvs (let () rhss ...))
                      (set-box! fvs-box fvs)
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
  (struct name exp (fields ...) #:transparent #:methods #,(syntax-local-introduce #'gen:binds-variables) [methods ...]))
(exp-struct var (name)
        [(def-free e free #:bound bound [(var x) (if (x . ∈ . bound) ∅ (set x))])])
(exp-struct lrc (xs es e)
            [(def-free e free #:gfree gfree #:bound bound 
              [(lrc xs es e)
               (define bound* (∪/l bound xs))
               (define (free* v) (gfree v #:bound bound*))
               (∪ ((union-map free*) es) (free* e))])])
(exp-struct lam (xs exp)
        [(def-free e free #:gfree gfree #:bound bound [(lam xs e) (gfree e #:bound (∪/l bound xs))])])
(exp-struct rlm (xs rest exp)
        [(def-free e free #:gfree gfree #:bound bound
           [(rlm xs rest e) (gfree e #:bound (∪/l bound (cons rest xs)))])])
(exp-struct app (ℓchk rator rand)
        [(def-free e free #:self free* #:bound bound [(app _ e0 es) (∪ (free* e0) ((union-map free*) es))])])
(exp-struct ife (t c a)
        [(def-free e free #:self free* [(ife g t e) (∪ (free* g) (free* e) (free* e))])])
(exp-struct st! (x e)
        [(def-free e free #:self free* #:bound bound
           [(st! x e) (∪ (free* e) (if (x . ∈ . bound) ∅ (set x)))])])
(exp-struct lcc (x e)
        [(def-free e free #:gfree gfree #:bound bound [(lcc x e) (gfree e #:bound (∪1 bound x))])])
;; Stack inspection forms
(exp-struct grt (r e)
        [(def-free e free #:self free* [(grt _ e) (free* e)])])
(exp-struct fal () [])
(exp-struct frm (r e)
        [(def-free e free #:self free* [(frm _ e) (free* e)])])
(exp-struct tst (r t e)
        [(def-free e free #:self free* [(tst _ t e) (∪ (free* t) (free* e))])])
;; Contract monitoring forms
(exp-struct mon (ℓchk pℓ nℓ sℓ s e)
        [(def-free e free #:self free* [(mon _ _ _ _ s e) (∪ (free* s) (free* e))])])
(exp-struct tmon (ℓchk pℓ nℓ sℓ s t e)
        [(def-free e free #:self free* [(tmon _ _ _ _ s _ e) (∪ (free* s) (free* e))])])
;; Structural contract constructors
(exp-struct consc (ca cd)
        [(def-free e free #:self free* [(consc ca cd) (∪ (free* ca) (free* cd))])])
(exp-struct andc (c₀ c₁)
        [(def-free e free #:self free* [(andc c₀ c₁)  (∪ (free* c₀) (free* c₁))])])
(exp-struct orc (c₀ c₁)
        [(def-free e free #:self free* [(orc c₀ c₁)  (∪ (free* c₀) (free* c₁))])])
(exp-struct fltc (e)
        [(def-free e free #:self free* [(fltc e) (free* e)])])
(exp-struct arrc (name ncs pc)
            [(def-free e free #:self free* [(arrc _ ncs pc) (∪ ((union-map free*) ncs) (free* pc))])])
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
;; Merged versions of data that must be evaluated specially.
(exp-struct mk-list^ (vals) [])
(exp-struct mk-improper^ (vals last) [])
(exp-struct mk-vector^ (vals) [])
(exp-struct mk-hash^ (keys vals) [])
