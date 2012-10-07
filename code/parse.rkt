#lang racket
(provide parse parse-prog)
(require "ast.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (parse-prog los)
  (match los
    [(list e) (parse e)]
    [(list ds ... e)
     (define bs (parse-defns ds))
     (parse `(letrec ,bs ,e))]))

(define (parse-defns ds)
  (match ds
    ['() '()]
    [`((define (,f ,x) . ,b) . ,ds)
     (parse-defns `((define ,f (lambda (,x) . ,b)) . ,ds))]
    [`((define ,f ,e) . ,ds)
     (cons (list f e)
           (parse-defns ds))]))
       
(define (op1-name? x)
  (memq x '(add1 sub1 zero? not)))

(define (op2-name? x)
  (memq x '(*)))

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
    [`(rec ,f ,e) ;; KILLME
     (rec f (parse e))]
    [`(,(? op1-name? o) ,e)
     (1op (gensym) o (parse e))]    
    [`(,(? op2-name? o) ,e0 ,e1)
     (2op (gensym) o (parse e0) (parse e1))]
    [`(,e0 ,e1)
     (app (gensym)
          (parse e0)
          (parse e1))]
    [(? boolean? b) (bln (gensym) b)]
    [(? number? n) (num (gensym) n)]
    [(? symbol? s) (var (gensym) s)]))