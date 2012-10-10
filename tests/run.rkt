#lang racket
(require rackunit)

(require "../code/parse.rkt")
(require "../benchmarks/progs.rkt")

(require "../code/kcfa.rkt"
	 #;(prefix-in lazy: "../code/0cfa-lazy.rkt")
	 #;(prefix-in delta: "../code/0cfa-delta.rkt"))


(define (check-∈ x xs) (check set-member? xs x))
(define (check-⊑ x xs)
  (check (λ (xs x) 
           (or (set-member? xs x)
               (set-member? xs (widen x))))
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
  (check->> '[((lambda (x) x) 3)] 3)
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

(simple-tests eval (λ (x) x))
(simple-tests lazy-eval (λ (x) x)) ; laziness not working yet
(simple-tests 0cfa widen)
(simple-tests 0cfa^ widen)
(simple-tests lazy-0cfa widen)
(simple-tests lazy-0cfa^ widen)
(simple-tests 1cfa widen)
(simple-tests 1cfa^ widen)
(simple-tests lazy-1cfa widen)
(simple-tests lazy-1cfa^ widen)

  
;(check-in #t (eval (parse-prog church))) ; expensive
(check-∈ #f (eval (parse-prog vhm08)))

(check-∈  2 (eval (parse-prog mj09)))
(check-∈ #f (eval (parse-prog eta)))
(check-∈ #f (eval (parse-prog kcfa2)))
(check-∈ #f (eval (parse-prog kcfa3)))
(check-∈ #f (eval (parse-prog blur)))
;(check-∈ 550 (eval (parse-prog loop2))) ; too expensive
(check-∈ #t (eval (parse-prog sat)))          

;(check-in #t (0cfa^ (parse-prog church))) ; expensive
(check-∈ #f  (0cfa^ (parse-prog vhm08)))

(check-∈  2  (0cfa^ (parse-prog mj09)))
(check-∈ #f  (0cfa^ (parse-prog eta)))
(check-∈ #f  (0cfa^ (parse-prog kcfa2)))
(check-∈ #f  (0cfa^ (parse-prog kcfa3)))
(check-∈ #f  (0cfa^ (parse-prog blur)))
;(check-∈ 550 (0cfa^ (parse-prog loop2))) ; too expensive
(check-∈ #t  (0cfa^ (parse-prog sat)))


;; mutually recursive top-level functions
(check-∈ #t 
          (eval
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

(check-∈ 3 (0cfa^ (parse '(letrec ((f (lambda (z) x)) (x 3)) (f 1)))))
(check-∈ 3 (0cfa^ (parse '(letrec ((x 3) (f (lambda (z) x))) (f 1)))))

#|
;; Check result of evaluation against analysis

(check-in 2 (delta:0cfa^ (parse-prog mj09)))
(check-in #t (delta:0cfa^ (parse-prog church)))

(check-in 2 (0cfa^ (parse-prog mj09)))
(check-in 2 (lazy:0cfa^ (parse-prog mj09)))
(check-in #f (lazy:0cfa^ (parse-prog blur)))
(check-in #f (delta:0cfa^ (parse-prog blur)))
|#
;; run parser tests
(require "parse.rkt")
