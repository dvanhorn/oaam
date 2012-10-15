#lang racket

(provide rkt->sexp sch->sexp)

;; expect top level forms
(define (sch->sexp file)
  (top-level->sexp
   (parameterize ([current-namespace (make-base-namespace)])
     (with-input-from-file file
       (lambda () (for/list ([form (in-port read-syntax)])
                    (syntax->datum (expand form))))))))
;; expect a #lang and module stuff.
(define (rkt->sexp file)
  (match (syntax->datum
          (parameterize ([read-accept-reader #t] ;; #lang ok
                         [current-namespace (make-base-namespace)])
            (expand (with-input-from-file file read-syntax))))
    [`(module ,name ,path (#%module-begin ,forms ...))
     ;; ignore provide/require forms
     (top-level->sexp (filter (match-lambda [(or `(#%provide . ,rest)
                                                 `(#%require . ,rest)) #f]
                                            [_ #t])
                              forms))]))

(define (top-level->sexp forms)
  (define-values (defs exps)
    (split-at-right forms 1))
  (append (for/list ([def defs]) (define-values->sexp def))
          (list (expr->sexp (car exps)))))

(define (define-values->sexp sexp)
  (match sexp
    [`(define-values (,id) ,body)
     `(define ,id ,(expr->sexp body))]
    [_ (error 'define-values->sexp "Bad define ~a" sexp)]))

(define (expr->sexp sexp)
  (match sexp
    [`(let-values ([(,ids) ,es] ...) ,body ...)
     `(let ,(for/list ([id ids] [e es]) `[,id ,(expr->sexp e)])
        ,(expr->sexp `(begin . ,body)))]
    [`(begin ,e) (expr->sexp e)]
    [`(begin ,e . ,es) 
     `((lambda (,(gensym '_)) ,(expr->sexp `(begin ,@es))) ,(expr->sexp e))]
    [`(letrec-values ([(,ids) ,es] ...) ,body)
     `(letrec ,(for/list ([id ids] [e es]) `[,id ,(expr->sexp e)])
        ,(expr->sexp body))]
    [`(if ,g ,t ,e)
     `(if ,(expr->sexp g) ,(expr->sexp t) ,(expr->sexp e))]
    [`(set! ,x ,e) `(set! ,x ,(expr->sexp e))]
    [(or `(#%plain-app ,es ...)
         `(#%app ,es ...))
     (map expr->sexp es)]
    [(or `(#%plain-lambda (,xs ...) ,body ...)
         `(lambda (,xs ...) ,body ...))
     `(lambda ,xs ,(expr->sexp `(begin . ,body)))]
    [`(quote ,d) sexp]
    [(? symbol? x) x]
    [`(#%top . ,(? symbol? x)) x]
    [_ (error 'expr->sexp "Bad or unsupported form ~a" sexp)]))
