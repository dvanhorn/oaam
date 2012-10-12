#lang racket

(provide (struct-out exp)
         (struct-out var)
         (struct-out num)
         (struct-out bln)
         (struct-out lam)
         (struct-out app)
         (struct-out rec)
         (struct-out ife)
         (struct-out 1op)
         (struct-out 2op)
         parse)
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
(struct lam exp (var exp)    #:transparent)
(struct app exp (rator rand) #:transparent)
(struct rec (name fun)       #:transparent)
(struct ife exp (t c a)      #:transparent)
(struct 1op exp (o a)        #:transparent)
(struct 2op exp (o a b)      #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (parse sexp fresh-label! fresh-variable!)
  (let parse ([sexp sexp]
               [ρ (hash)])
     (define (parse* sexp) (parse sexp ρ))
     (match sexp
       [`(let* () ,e) (parse* e)]
       [`(let* ((,x ,e) . ,r) ,b)
        (parse* `((lambda (,x) (let* ,r ,b)) ,e))]
       [`(lambda (,x) ,e)
        (define x-lab (fresh-variable! x))
        (lam (fresh-label!) x-lab (parse e (hash-set ρ x x-lab)))]
       [`(if ,e0 ,e1 ,e2)
        (ife (fresh-label!) (parse* e0) (parse* e1) (parse* e2))]
       [`(rec ,f ,e)
        (define f-lab (fresh-variable! f))
        (rec f-lab (parse e (hash-set ρ f f-lab)))]
       [`(sub1 ,e)
        (1op (fresh-label!) 'sub1 (parse* e))]
       [`(add1 ,e)
        (1op (fresh-label!) 'add1 (parse* e))]
       [`(zero? ,e)
        (1op (fresh-label!) 'zero? (parse* e))]
       [`(* ,e0 ,e1)
        (2op (fresh-label!) '* (parse* e0) (parse* e1))]
       [`(,e0 ,e1)
        (app (fresh-label!)
             (parse* e0)
             (parse* e1))]
       [(? boolean? b) (bln (fresh-label!) b)]
       [(? number? n) (num (fresh-label!) n)]
       [(? symbol? s) (var (fresh-label!) (hash-ref ρ s (λ () (error 'parse "Open program: ~a" s))))])))