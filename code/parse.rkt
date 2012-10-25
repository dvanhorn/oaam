#lang racket
(provide parse parse-prog unparse)
(require "ast.rkt" "primitives.rkt" "data.rkt" "macros.rkt"
         racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (parse-prog sexp [fresh-label! igensym] [fresh-variable! igensym])
  (parse (cons define-ctx sexp) fresh-label! fresh-variable!))

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
  (define expr
    (let parse* ([sexp sexp]
                 [ρ (hasheq)])
      (define (parse sexp) (parse* sexp ρ))
      (define ((parse_ ρ) sexp) (parse* sexp ρ))
      (define (rename x) (hash-ref ρ x (new-free x)))
      (define (parse-seq s [ρ ρ]) (parse* (define-ctx-tf s) ρ))
      (define (fresh-xs xs)
        (define xs-id (map fresh-variable! xs))
        (values xs-id
                (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id))))
      (define (parse-core sexp)
        (match sexp
          [`(set! ,x ,e) (st! (fresh-label!) (rename x) (parse e))]
          [`(letrec () . ,s) (parse-seq s)]
          [`(letrec ((,xs ,es) ...) . ,s)
           (define-values (xs-id ρ) (fresh-xs xs))
           (lrc (fresh-label!) xs-id (map (parse_ ρ) es) (parse-seq s ρ))]
          [`(lambda (,xs ...) . ,s)
           (define-values (xs-id ρ) (fresh-xs xs))
           (lam (fresh-label!) xs-id (parse-seq s ρ))]
          [`(lambda (,xs ... . ,rest) . ,s)
           (define-values (xs-id ρ) (fresh-xs xs))
           (define r-id (fresh-variable! rest))
           (rlm (fresh-label!) xs-id r-id (parse-seq s (hash-set ρ rest r-id)))]
          [`(lambda ,x . ,s)
           (define x-id (fresh-variable! x))
           (rlm (fresh-label!) '() x-id (parse-seq s (hash-set ρ x x-id)))]
          [`(if ,e0 ,e1 ,e2)
           (ife (fresh-label!) (parse e0) (parse e1) (parse e2))]
          [`(if ,g ,t)
           (printf "Warning: If without else: ~a~%" sexp)
           (parse-core `(if ,g ,t (,void$)))]
          [`(,(or 'lambda 'if 'letrec 'set!) . ,rest)
           (error 'parse-core "Ill-formed core form ~a" sexp)]
          [`(,(== kwote) ,d) (datum (fresh-label!) d)]
          [`(,(== define-ctx) . ,forms) (parse-seq forms)]
          [`(,s . ,es) (=> fail)
           (match (hash-ref macro-env s #f)
             [#f (fail)]
             [tf (parse (tf sexp))])]
          [`(,e . ,es)
           (app (fresh-label!) (parse e) (map parse es))]))

      (match sexp
        [`(,(== special) . ,s) (primr (fresh-label!) s)]
        [`((,(== special) . ,s) . ,es)
         (if (primitive? s)
             (primr (fresh-label!) s)
             (parse-core (cons s es)))]
        [`(,e . ,es)
         (cond [(hash-has-key? ρ e)
                (app (fresh-label!)
                     (var (fresh-label!) (rename e))
                     (map parse es))]               
               [else (parse-core sexp)])]
        [(? symbol? s)
         (define (mkvar) (var (fresh-label!) (rename s)))
         (cond [(not (hash-has-key? ρ s))
                (cond [(primitive? s) (primr (fresh-label!) s)]
                      [(hash-ref prim-constants s #f) =>
                       (λ (d) (datum (fresh-label!) d))]
                      [else (mkvar)])]
               [else (mkvar)])]
        [(? atomic? d) (datum (fresh-label!) d)]
        [err (error 'parse "Unknown form ~a" err)])))
  (values expr open))
#;
(trace parse)
(define (unparse e)
  (match e
    [(or (var _ x) (datum _ x) (primr _ x)) x]
    [(app _ e es) (map unparse (cons e es))]
    [(lam _ xs body) `(λ ,xs ,(unparse body))]
    [(ife _ g t e) `(if ,(unparse g) ,(unparse t) ,(unparse e))]
    [(st! _ x e) `(set! ,x ,(unparse e))]
    [(lrc _ xs es body) `(letrec ,(map list xs (map unparse es)) ,(unparse body))]
    [_ (error 'unparse "Bad exp ~a" e)]))