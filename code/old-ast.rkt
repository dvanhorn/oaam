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

(define (parse sexp set-nlabels!)
  (define nlabels 0)
  (define (next-label!)
    (begin0 nlabels
            (set! nlabels (add1 nlabels))))
  (begin0
   (let parse ([sexp sexp]
               [ρ (hash)])
     (define (parse* sexp) (parse sexp ρ))
     (match sexp
       [`(let* () ,e) (parse* e)]
       [`(let* ((,x ,e) . ,r) ,b)
        (parse* `((lambda (,x) (let* ,r ,b)) ,e))]
       [`(lambda (,x) ,e)
        (define x-lab (next-label!))
        (lam (next-label!) x-lab (parse e (hash-set ρ x x-lab)))]
       [`(if ,e0 ,e1 ,e2)
        (ife (next-label!) (parse* e0) (parse* e1) (parse* e2))]
       [`(rec ,f ,e)
        (define f-lab (next-label!))
        (rec f-lab (parse e (hash-set ρ f f-lab)))]
       [`(sub1 ,e)
        (1op (next-label!) 'sub1 (parse* e))]
       [`(add1 ,e)
        (1op (next-label!) 'add1 (parse* e))]
       [`(zero? ,e)
        (1op (next-label!) 'zero? (parse* e))]
       [`(* ,e0 ,e1)
        (2op (next-label!) '* (parse* e0) (parse* e1))]
       [`(,e0 ,e1)
        (app (next-label!)
             (parse* e0)
             (parse* e1))]
       [(? boolean? b) (bln (next-label!) b)]
       [(? number? n) (num (next-label!) n)]
       [(? symbol? s) (var (next-label!) (hash-ref ρ s (λ () (error 'parse "Open program: ~a" s))))]))
   (set-nlabels! nlabels)))