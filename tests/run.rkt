#lang racket
(require rackunit)

(require "../code/parse.rkt")
(require "../benchmarks/progs.rkt")

(require (prefix-in 0cfa: "../code/0cfa.rkt")
	 #;(prefix-in lazy: "../code/0cfa-lazy.rkt")
	 #;(prefix-in delta: "../code/0cfa-delta.rkt"))


(define (check-∈ x xs) (check set-member? xs x))
(define (check-⊑ x xs)
  (check (λ (xs x) 
           (or (set-member? xs x)
               (set-member? xs (0cfa:widen x))))
         xs
         x))

(define (overlap? s1 s2)
  (not (set-empty? (set-intersect s1 s2))))

(define (simple-tests ev widen)
  (define (check->> p x) (check overlap? 
                                (set x (widen x)) 
                                (ev (parse-prog p))))
  
  (check->> '[#t] #t)
  (check->> '[(or #t)] #t)
  (check->> '[(or #f)] #f)
  (check->> '[(= 4 4)] #t)
  (check->> '[(= 4 3)] #f)
  (check->> '[(letrec ((f (lambda (z) x)) (x 3)) (f 1))]
            3)
  (check->> '[(define x 1)
              (set! x 2)
              x]
            2)
  (check->> '[(define (fact n)
                (if (zero? n)
                    1
                    (* n (fact (sub1 n)))))
              (fact 5)]
            120))

(simple-tests 0cfa:eval (λ (x) x))
(simple-tests 0cfa:aval^ 0cfa:widen)
  
;(check-in #t (0cfa:eval (parse-prog church))) ; expensive
(check-∈ #f (0cfa:eval (parse-prog vhm08)))

(check-∈  2 (0cfa:eval (parse-prog mj09)))
(check-∈ #f (0cfa:eval (parse-prog eta)))
(check-∈ #f (0cfa:eval (parse-prog kcfa2)))
(check-∈ #f (0cfa:eval (parse-prog kcfa3)))
(check-∈ #f (0cfa:eval (parse-prog blur)))
;(check-∈ 550 (0cfa:eval (parse-prog loop2))) ; too expensive
(check-∈ #t (0cfa:eval (parse-prog sat)))          

;(check-in #t (0cfa:aval^ (parse-prog church))) ; expensive
(check-∈ #f  (0cfa:aval^ (parse-prog vhm08)))

(check-∈  2  (0cfa:aval^ (parse-prog mj09)))
(check-∈ #f  (0cfa:aval^ (parse-prog eta)))
(check-∈ #f  (0cfa:aval^ (parse-prog kcfa2)))
(check-∈ #f  (0cfa:aval^ (parse-prog kcfa3)))
(check-∈ #f  (0cfa:aval^ (parse-prog blur)))
;(check-∈ 550 (0cfa:aval^ (parse-prog loop2))) ; too expensive
(check-∈ #t  (0cfa:aval^ (parse-prog sat)))


;; mutually recursive top-level functions
(check-∈ #t 
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

(check-∈ 3 (0cfa:aval^ (parse '(letrec ((f (lambda (z) x)) (x 3)) (f 1)))))
(check-∈ 3 (0cfa:aval^ (parse '(letrec ((x 3) (f (lambda (z) x))) (f 1)))))

#|
;; Check result of evaluation against analysis

(check-in 2 (delta:aval^ (parse-prog mj09)))
(check-in #t (delta:aval^ (parse-prog church)))

(check-in 2 (0cfa:aval^ (parse-prog mj09)))
(check-in 2 (lazy:aval^ (parse-prog mj09)))
(check-in #f (lazy:aval^ (parse-prog blur)))
(check-in #f (delta:aval^ (parse-prog blur)))
|#
;; run parser tests
(require "parse.rkt")
