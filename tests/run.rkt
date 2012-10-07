#lang racket
(require rackunit)

(require "../code/parse.rkt")
(require "../benchmarks/progs.rkt")

(require (prefix-in 0cfa: "../code/0cfa.rkt")
	 (prefix-in lazy: "../code/0cfa-lazy.rkt")
	 (prefix-in delta: "../code/0cfa-delta.rkt"))


(define (check-in x xs) (check set-member? xs x))

(check-in 3 (0cfa:eval  (parse '(letrec ((f (lambda (z) x)) (x 3)) (f 1)))))
(check-in 120
          (0cfa:eval
           (parse-prog
            '[(define (fact n)
                (if (zero? n)
                    1
                    (* n (fact (sub1 n)))))
              (fact 5)])))

;; mutually recursive top-level functions
(check-in #t 
          (0cfa:eval
           (parse-prog
            '[(define (even? x)
                (if (zero? x)
                    #t
                    (not (odd? (sub1 x)))))
              (define (odd? y)
                (if (zero? y)
                    #f
                    (not (even? (sub1 y)))))
              (even? 2)])))

(check-in 3 (0cfa:aval^ (parse '(letrec ((f (lambda (z) x)) (x 3)) (f 1)))))
(check-in 3 (0cfa:aval^ (parse '(letrec ((x 3) (f (lambda (z) x))) (f 1)))))

;; Check result of evaluation against analysis

(check-in 2 (delta:aval^ (parse-prog mj09)))
(check-in #t (delta:aval^ (parse-prog church)))

(check-in 2 (0cfa:aval^ (parse-prog mj09)))
(check-in 2 (lazy:aval^ (parse-prog mj09)))
(check-in #f (lazy:aval^ (parse-prog blur)))
(check-in #f (delta:aval^ (parse-prog blur)))

;; run parser tests
(require "parse.rkt")
