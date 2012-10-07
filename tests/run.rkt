#lang racket
(require rackunit)

(require "../code/parse.rkt")
(require (prefix-in mj09: "../benchmarks/midtgaard-jensen09.rkt")
	 (prefix-in church: "../benchmarks/church-example.rkt")
	 (prefix-in blur: "../benchmarks/church-example.rkt"))

(require (prefix-in 0cfa: "../code/0cfa.rkt")
	 (prefix-in lazy: "../code/0cfa-lazy.rkt")
	 (prefix-in delta: "../code/0cfa-delta.rkt"))


(define (check-in x xs) (check set-member? xs x))

(check-in 3 (0cfa:eval  (parse '(letrec ((f (lambda (z) x)) (x 3)) (f 1)))))
(check-in 3 (0cfa:aval^ (parse '(letrec ((f (lambda (z) x)) (x 3)) (f 1)))))
(check-in 3 (0cfa:aval^ (parse '(letrec ((x 3) (f (lambda (z) x))) (f 1)))))

;; Check result of evaluation against analysis

(check-in 2 (delta:aval^ (parse mj09:P)))
(check-in #t (delta:aval^ (parse church:P)))

(check-in 2 (0cfa:aval^ (parse mj09:P)))
(check-in 2 (lazy:aval^ (parse mj09:P)))
(check-in #f (lazy:aval^ (parse blur:P)))
(check-in #f (delta:aval^ (parse blur:P)))

;; run parser tests
(require "parse.rkt")
