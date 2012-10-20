#lang racket

(require "parse.rkt" "kcfa-instantiations.rkt" "racket-to-sexp.rkt"
         racket/trace)

(define (prep! file) (sch->sexp file))
(define (prep-sexp! sexp) (expand-sexp-prog sexp))
;(trace prep)

(define (prep-sexp sexp) (parse-prog (expand-sexp-prog sexp)))
(define (prep file) (parse-prog (sch->sexp file)))

(define eval lazy-0cfa^/c)
#|
 (eval (prep-sexp '(
                    (let ([x '0])
                      (set! x '1)
                      (if (zero? x) (set! x '1) (void))
                      x))))

 (eval (prep-sexp '(
                    (((lambda (fn) (lambda (data) (fn data)))
                      (lambda (x) (cdar (cddr x))))
                     '((a . 0)
                       (b . 1)
                       (c . 2))))))

 (eval (prep-sexp '(
                   (let* ([x (cons '0 '1)]
                          [y (car x)]
                          [_ (set-car! x '2)])
                     (cons y (car x))))))

 (eval (prep-sexp '(
                   (let ([x '((a . 0)
                              (b . 1)
                              (c . 2))])
                     (list (caar x)
                           (begin (set-car! x '(a* . 10))
                                  (cdr x)))))))
|#


(time (eval (prep "../benchmarks/church.sch")))
(time (lazy-0cfa^ (prep "../benchmarks/church.sch")))
(time (lazy-0cfa∆/c (prep "../benchmarks/church.sch")))
(time (lazy-0cfa^-gen-σ-∆s/c (prep "../benchmarks/church.sch")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/church.sch")))
#;
(time
 (eval (prep "../benchmarks/toplas98/boyer.sch")))
