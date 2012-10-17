#lang racket
(provide parse parse-prog)
(require "ast.rkt" "primitives.rkt" "data.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (parse-prog los [fresh-label! gensym] [fresh-variable! gensym])
  (match los
    [(list e) (parse e fresh-label! fresh-variable!)]
    [(list (and ds `(define ,_ . ,_)) ... es ...)
     (define bs (parse-defns ds))     
     (parse `(letrec ,bs (begin ,@es)) fresh-label! fresh-variable!)]))

(define (parse-defns ds)
  (match ds
    ['() '()]
    [`((define (,f . ,xs) . ,b) . ,ds)
     (parse-defns `((define ,f (lambda ,xs . ,b)) . ,ds))]
    [`((define ,f ,e) . ,ds)
     (cons (list f e)
           (parse-defns ds))]))

(define (parse sexp [fresh-label! gensym] [fresh-variable! gensym])
  (let parse* ([sexp sexp]
               [ρ (hasheq)])
    (define (parse sexp) (parse* sexp ρ))
    (define ((parse_ ρ) sexp) (parse* sexp ρ))
    (define (rename x) (hash-ref ρ x (λ () (error 'parse "Unbound variable ~a" x))))
    (define (parse-seq s [ρ ρ]) (parse* (cons 'begin s) ρ))
    (define (fresh-xs xs)
      (define xs-id (map fresh-variable! xs))
      (values xs-id
              (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id))))
    (match sexp
      [`(begin ,e) (parse e)]
      [`(begin ,e . ,r)
       (parse `((lambda (,(gensym)) (begin . ,r)) ,e))]
      [`(let () . ,b) (parse-seq b)]
      [`(let ((,xs ,es) ...) . ,b)
       (parse `((lambda ,xs . ,b) . ,es))]
      [`(set! ,x ,e) (st! (fresh-label!) (rename x) (parse e))]
      [`(letrec () . ,s) (parse-seq s)]
      [`(letrec ((,xs ,es) ...) . ,s)
       (define-values (xs-id ρ) (fresh-xs xs))
       (lrc (fresh-label!) xs-id (map (parse_ ρ) es) (parse-seq s ρ))]
      [`(letrec* () . ,s) (parse s)] ;; our letrec is letrec*
      [`(letrec* ((,xs ,es) ...) . ,s)
       (define-values (xs-id ρ) (fresh-xs xs))
       (lrc (fresh-label!) xs-id (map (parse_ ρ) es) (parse-seq s ρ))]
      [`(lambda ,xs . ,s)
       (define-values (xs-id ρ) (fresh-xs xs))
       (lam (fresh-label!) xs-id (parse-seq s ρ))]
      [`(if ,e0 ,e1 ,e2)
       (ife (fresh-label!) (parse e0) (parse e1) (parse e2))]
      [`(quote ,d)
       (cond
         [(hash-has-key? ρ 'quote) ;; was rebound
          (app (fresh-label!)
               (var (fresh-label!) (rename 'quote))
               (list (parse d)))]
         [(atomic? d) (datum (fresh-label!) d)]
         ;; List literals get exploded into conses
         [(pair? d) (parse `(cons (quote ,(car d)) (quote ,(cdr d))))]
         [else (error 'parse "Unsupported datum ~a" d)])]
      [`(,e . ,es)
       (app (fresh-label!)
            (parse e)
            (map parse es))]
      [(? symbol? s)
       (if (and (primitive? s)
                (not (hash-has-key? ρ s)))
         (primr (fresh-label!) s)
         (var (fresh-label!) (rename s)))]
      [(? atomic? d) (datum (fresh-label!) d)]
      [err (error 'parse "Unknown form ~a" err)])))
