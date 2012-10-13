#lang racket
(provide parse parse-prog)
(require "ast.rkt" "primitives.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (parse-prog los)
  (match los
    [(list e) (parse e)]
    [(list (and ds `(define ,_ . ,_)) ... es ...)
     (define bs (parse-defns ds))
     (parse `(letrec ,bs (begin ,@es)))]))

(define (parse-defns ds)
  (match ds
    ['() '()]
    [`((define (,f . ,xs) . ,b) . ,ds)
     (parse-defns `((define ,f (lambda ,xs . ,b)) . ,ds))]
    [`((define ,f ,e) . ,ds)
     (cons (list f e)
           (parse-defns ds))]))

(define (parse sexp fresh-label! fresh-variable!)
  (let parse* ([sexp sexp]
              [ρ (hasheq)])
    (define (parse sexp) (parse* sexp ρ))
    (define (rename x)
      (hash-ref ρ x (λ () (error 'parse "Unbound variable ~a" x))))
    (define (parse-seq s [ρ ρ]) (parse* (cons 'begin s) ρ))
    (match sexp
      [`(begin ,e) (parse e)]
      [`(begin ,e . ,r)
       (parse `((lambda (,(gensym)) (begin . ,r)) ,e))]
      [`(let () . ,b)
       (parse `(begin . ,b))]
      [`(let ((,xs ,es) ...) . ,b)
       (parse `((lambda ,xs . ,b) . ,es))]
      [`(let* () . ,s) (parse-seq s)]
      [`(let* ((,x ,e) . ,r) . ,b)
       (define x-id (fresh-variable!))
       (app (fresh-label!)
            (lam (fresh-label!)
                 (list x-id)
                 (parse* `(let* ,r ,@b) (hash-set ρ x x-id)))
            (list (parse e)))]
      [`(set! ,x ,e) (st! (fresh-label!) (rename x) (parse e))]
      [`(letrec () . ,s) (parse-seq s)]
      [`(letrec ((,xs ,es) ...) . ,s)
       (define xs-id (map fresh-variable xs))
       (define ρ* (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id)))
       (lrc (fresh-label!) xs (map (λ (e) (parse* e ρ*)) es) (parse-seq s ρ*))]
      [`(letrec* () . ,s) (parse s)] ;; our letrec is letrec*
      [`(letrec* ((,xs ,es) ...) . ,s)
       (define xs-id (map fresh-variable xs))
       (define ρ* (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id)))
       (lrc (fresh-label!) xs-id (map (λ (e) (parse* e ρ*)) es) (parse-seq s ρ*))]
      [`(lambda ,xs . ,s)
       (define xs-id (map fresh-variable xs))
       (define ρ* (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id)))
       (lam (fresh-label!) xs-id (parse-seq s ρ*))]
      [`(cond ((else ,a1))) (parse a1)]
      [`(cond ((,q1 ,a1) . ,r))
       (parse `(if ,q1 ,a1 (cond . ,r)))]
      [`(cond ((,q1 ,a1) . r))
       (parse `(if ,q1 ,a1 (cond . r)))]
      [`(cond) (parse 0)] ;; FIXME
      [`(if ,e0 ,e1 ,e2)
       (ife (fresh-label!) (parse e0) (parse e1) (parse e2))]
      [`(rec ,f ,e) ;; KILLME
       (define f-id (fresh-variable!))
       (rec f-id (parse* e (hash-set ρ* f f-id)))]
      [`(and) (parse #f)]
      [`(and ,e) (parse e)]
      [`(and ,e . ,es)
       (parse `(if ,e (and ,@es) #f))]
      [`(or) (parse #t)]
      [`(or ,e) (parse e)]
      [`(or ,e . ,es)
       (define tmp (gensym)) ;; FIXME don't generate names
       (parse `(let ((,tmp ,e))
                 (if ,tmp ,tmp (or ,@es))))]
      [`(,e . ,es)
       (app (fresh-label!)
            (parse e)
            (map parse es))]
      [(? boolean? b) (bln (fresh-label!) b)]
      [(? number? n) (num (fresh-label!) n)]
      [(? symbol? s)
       (cond [(hash-has-key? ρ s) (var (fresh-label!) (rename s))]
             [(primitive? s) (primr (fresh-label!) s)]
             [else (rename s) #;will-error])])))
