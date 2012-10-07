#lang racket
(provide (all-defined-out))

;; An Exp is one of:
;; (var Lab Exp)
;; (num Lab Number)
;; (bln Lab Boolean)
;; (lam Lab Sym Exp)
;; (app Lab Exp Exp)
;; (rec Sym Lam)
;; (if Lab Exp Exp Exp)
(struct exp (lab)            #:transparent)
(struct var exp (name)       #:transparent)
(struct num exp (val)        #:transparent)
(struct bln exp (b)          #:transparent)
(struct lrc exp (xs es e)    #:transparent)
(struct lam exp (var exp)    #:transparent)
(struct app exp (rator rand) #:transparent)
(struct rec (name fun)       #:transparent)
(struct ife exp (t c a)      #:transparent)
(struct 1op exp (o a)        #:transparent)
(struct 2op exp (o a b)      #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (parse sexp)
  (match sexp
    [`(begin ,e) (parse e)]
    [`(begin ,e . ,r)
     (parse `((lambda (,(gensym)) (begin . ,r)) ,e))]
    ;; only handle single let
    [`(let ((,x ,e)) ,b)
     (parse `((lambda (,x) ,b) ,e))]
    [`(let* () ,e) (parse e)]
    [`(let* ((,x ,e) . ,r) ,b)
     (app (gensym)
          (lam (gensym) x (parse `(let* ,r ,b)))
          (parse e))]
    [`(letrec () ,e) (parse e)]
    [`(letrec ((,xs ,es) ...) ,e)
     (lrc (gensym) xs (map parse es) (parse e))]
    [`(letrec* () ,e) (parse e)] ;; our letrec is letrec*
    [`(letrec* ((,xs ,es) ...) ,e)
     (lrc (gensym) xs es e)]
    [`(lambda (,x) ,e)
     (lam (gensym) x (parse e))]
    [`(cond ((else ,a1))) (parse a1)]
    [`(cond ((,q1 ,a1) . ,r))
     (parse `(if ,q1 ,a1 (cond . ,r)))]
    [`(cond ((,q1 ,a1) . r))
     (parse `(if ,q1 ,a1 (cond . r)))]
    [`(cond) (parse 0)] ;; FIXME
    [`(if ,e0 ,e1 ,e2)
     (ife (gensym) (parse e0) (parse e1) (parse e2))]
    [`(rec ,f ,e)
     (rec f (parse e))]
    [`(sub1 ,e)
     (1op (gensym) 'sub1 (parse e))]
    [`(add1 ,e)
     (1op (gensym) 'add1 (parse e))]
    [`(not ,e)
     (1op (gensym) 'not (parse e))]
    [`(zero? ,e)
     (1op (gensym) 'zero? (parse e))]
    [`(* ,e0 ,e1)
     (2op (gensym) '* (parse e0) (parse e1))]
    [`(,e0 ,e1)
     (app (gensym)
          (parse e0)
          (parse e1))]
    [(? boolean? b) (bln (gensym) b)]
    [(? number? n) (num (gensym) n)]
    [(? symbol? s) (var (gensym) s)]))

