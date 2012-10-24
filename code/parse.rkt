#lang racket
(provide parse parse-prog unparse)
(require "ast.rkt" "primitives.rkt" "data.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (igensym [start 'g]) (string->symbol (symbol->string (gensym start))))

(define (parse-prog los [fresh-label! igensym] [fresh-variable! igensym])
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

(define (parse sexp [fresh-label! igensym] [fresh-variable! igensym])
  ;; in order for the renaming to work on open programs, we not only have to return
  ;; the renamed program, but also a map from free variables to their new names.
  (define open (make-hasheq))
  (define ((new-free x))
    (match (hash-ref open x #f)
      [#f (define x-id (fresh-variable! x))
          (hash-set! open x x-id)
          x-id]
      [s s]))
  (define e
    (let parse* ([sexp sexp]
                 [ρ (hasheq)])
      (define (parse sexp) (parse* sexp ρ))
      (define ((parse_ ρ) sexp) (parse* sexp ρ))
      (define (rename x) (hash-ref ρ x (new-free x)))
      (define (parse-seq s [ρ ρ]) (parse* (cons 'begin s) ρ))
      (define (fresh-xs xs)
        (define xs-id (map fresh-variable! xs))
        (values xs-id
                (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id))))
      (match sexp
        [`(begin ,e) (parse e)]
        [`(begin ,e . ,r)
         (parse `((lambda (,(igensym)) (begin . ,r)) ,e))]
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
        ;; different lambdas
        [`(,(or 'lambda 'λ) (,xs ...) . ,s)
         (define-values (xs-id ρ) (fresh-xs xs))
         (lam (fresh-label!) xs-id (parse-seq s ρ))]
        [`(,(or 'lambda 'λ) (,xs ... . ,rest) . ,s)
         (define-values (xs-id ρ) (fresh-xs xs))
         (define r-id (fresh-variable! rest))
         (rlm (fresh-label!) xs-id r-id (parse-seq s (hash-set ρ rest r-id)))]
        [`(,(or 'lambda 'λ) ,x . ,s)
         (define x-id (fresh-variable! x))
         (rlm (fresh-label!) '() x-id (parse-seq s (hash-set ρ x x-id)))]
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
          ;; Hash literals get exploded into hash-sets
          [(hash? d)
           (match (for/first ([kv (in-hash-pairs d)]) kv)
             [#f (datum (fresh-label!) (mthash (hash->kind d)))]
             [(cons k v)
              (parse `(hash-set (quote ,(hash-remove d k))
                                (quote ,k)
                                (quote ,v)))])]
          ;; Vector literals get exploded into an allocation and initialization
          ;; FIXME: incorrect for Racket. Need handling for immutable vectors.
          [(vector? d)
           (define tmp (gensym))
           (parse `(let ([,tmp (make-vector (quote ,(vector-length d)))])
                     ,@(for/list ([v (in-vector d)]
                                  [i (in-naturals)])
                         `(vector-set! ,tmp (quote ,i) (quote ,v)))))]
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
  (values e open))

(define (unparse e)
  (match e
    [(or (var _ x) (datum _ x) (primr _ x)) x]
    [(app _ e es) (map unparse (cons e es))]
    [(lam _ xs body) `(λ ,xs ,(unparse body))]
    [(ife _ g t e) `(if ,(unparse g) ,(unparse t) ,(unparse e))]
    [(st! _ x e) `(set! ,x ,(unparse e))]
    [(lrc _ xs es body) `(letrec ,(map list xs (map unparse es)) ,(unparse body))]))