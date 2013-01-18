#lang racket
(require "ast.rkt" "primitives.rkt" "data.rkt" "macros.rkt" "egal-box.rkt"
         racket/trace)
(provide parse parse-prog unparse internal-apply$
         simple-fresh-label! simple-fresh-variable! top-ctx)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define prim-fallbacks #f)
(define (simple-fresh-label! ctx new?) (gensym))
(define (simple-fresh-variable! x ctx) (gensym x))
(define top-ctx 'top)
(define (parse-prog sexp [fresh-label! simple-fresh-label!] [fresh-variable! simple-fresh-variable!])
  (set! prim-fallbacks (make-hasheq))
  (parse (cons define-ctx sexp) fresh-label! fresh-variable!))
#;
(trace parse-prog)

(define (parse sexp [fresh-label! igensym] [fresh-variable! igensym])
  ;; in order for the renaming to work on open programs, we not only have to return
  ;; the renamed program, but also a map from free variables to their new names.
  (define open (make-hasheq))
  (define prims-used (make-hasheq))
  (define (mk-primr tail? ctx which)
    (define b (hash-ref! prim-fallbacks which (λ () (ebox #f)) ))
    (primr (fresh-label! ctx #f) tail? which b))
  (define ((new-free x ctx))
    (match (hash-ref open x #f)
      [#f (define x-id (fresh-variable! x ctx))
          (hash-set! open x x-id)
          x-id]
      [s s]))
  (define expr
    (let parse* ([sexp sexp]
                 [tail? #t]
                 [ctx top-ctx]
                 [ρ (hasheq)])      
      (define (parse sexp tail?) (parse* sexp tail? ctx ρ))
      (define ((parse_ tail? [ρ ρ]) sexp) (parse* sexp tail? ctx ρ))
      (define (rename x) (hash-ref ρ x (new-free x ctx)))
      (define (parse-seq s tail? ctx [ρ ρ]) (parse* (define-ctx-tf s) tail? ctx ρ))
      (define (fresh-label*) (fresh-label! ctx #f))
      (define (fresh-variable* x) (fresh-variable! x ctx))
      (define (fresh-xs xs ctx)
        (define xs-id (map fresh-variable* xs))
        (values xs-id
                (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id))))
      (define (parse-core sexp)
        (match sexp
          [`(set! ,x ,e) (st! (fresh-label*) tail? (rename x) (parse e #f))]
          [`(letrec () . ,s) (parse-seq s tail? ctx)]
          [`(letrec ((,xs ,es) ...) . ,s)
           (define-values (xs-id ρ) (fresh-xs xs ctx))
           (lrc (fresh-label*) tail? xs-id (map (parse_ #f ρ) es) (parse-seq s tail? ctx ρ))]
          [`(lambda (,xs ...) . ,s)
           (define ctx* (fresh-label! ctx #t))
           (define-values (xs-id ρ) (fresh-xs xs ctx*))
           (lam ctx* tail? xs-id (parse-seq s #t ctx* ρ))]
          [`(lambda (,xs ... . ,rest) . ,s)
           (define ctx* (fresh-label! ctx #t))
           (define-values (xs-id ρ) (fresh-xs xs ctx*))
           (define r-id (fresh-variable! rest ctx*))
           (rlm ctx* tail? xs-id r-id (parse-seq s #t ctx* (hash-set ρ rest r-id)))]
          [`(lambda ,x . ,s)
           (define ctx* (fresh-label! ctx #t))
           (define x-id (fresh-variable! x ctx*))
           (rlm ctx* tail? '() x-id (parse-seq s #t ctx* (hash-set ρ x x-id)))]
          ;; Specialize let-like lambda
          [`((,(or 'lambda `(,(== special) . lambda)) () . ,body))
           (parse-seq body tail? ctx)]
          [(or `((,(or 'lambda `(,(== special) . lambda)) (,xs ...) . ,body) . ,es)
               `(core-let ([,xs ,es] ...) . ,body))
           (define-values (xs-id ρ*) (fresh-xs xs ctx))
           (unless (list? es)
             (error 'parse "Bad let ~a" sexp))
           (lte (fresh-label*) tail? xs-id (map (parse_ #f) es) (parse-seq body tail? ctx ρ*))]
          [`(if ,e0 ,e1 ,e2)
           (ife (fresh-label*) tail? (parse e0 #f) (parse e1 tail?) (parse e2 tail?))]
          [`(if ,g ,t)
           (printf "Warning: If without else: ~a~%" sexp)
           (parse-core `(if ,g ,t (,void$)))]
          [`(let/cc ,x ,e)
           (define x-id (fresh-variable* x))
           (lcc (fresh-label*) tail? x-id (parse* e tail? ctx (hash-set ρ x x-id)))]
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          ;; Continuation marks forms
          [`(test (,(? symbol? Rs) ...) ,t ,e)
           (tst (fresh-label*) tail? (list->set Rs) (parse t tail?) (parse e tail?))]
          [`(grant (,(? symbol? Rs) ...) ,e)
           (grt (fresh-label*) tail? (list->set Rs) (parse e #f))]
          ['(fail) (fal (fresh-label*) tail?)]
          [`(frame (,(? symbol? Rs) ...) ,e)
           (frm (fresh-label*) tail? (list->set Rs) (parse e #f))]
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          ;; End Continuation marks forms
          [`(,(or 'lambda 'if 'letrec 'set!
                  #;for-continuation-marks
                  'test 'grant 'fail 'frame) . ,rest)
           (error 'parse-core "Ill-formed core form ~a" sexp)]
          [`(,(== kwote) ,d) (datum (fresh-label*) tail? d)]
          [`(,(== define-ctx) . ,forms) (parse-seq forms tail? ctx)]
          [`(,s . ,es) (=> fail)
           (match (hash-ref macro-env s #f)
             [#f (fail)]
             [tf (parse (tf sexp) tail?)])]
          [`(,e . ,es)
           (unless (list? es)
             (error 'parse "Bad application ~a" sexp))
           (app (fresh-label*) tail? (parse e #f) (map (parse_ #f) es))]))

      (match sexp
        [`(,(== special) . ,s) (mk-primr tail? ctx s)]
        [`((,(== special) . ,s) . ,es)
         (cond [(primitive? s)
                (app (fresh-label*) tail?
                     (mk-primr #f ctx s)
                     (map (parse_ #f) es))]
               [else (parse-core (cons s es))])]
        [`(,e . ,es)
         (cond [(hash-has-key? ρ e)
                (app (fresh-label*) tail?
                     (var (fresh-label*) #f (rename e))
                     (map (parse_ #f) es))]
               [else (parse-core sexp)])]
        [(? symbol? s)
         (define (mkvar) (var (fresh-label*) tail? (rename s)))
         (cond [(hash-has-key? ρ s) (mkvar)]
               [(primitive? s) (mk-primr tail? ctx s)]
               [(hash-ref prim-constants s #f) =>
                (λ (d) (datum (fresh-label*) tail? d))]
               [else (mkvar)])] ;; will error
        [(? atomic? d) (datum (fresh-label*) tail? d)]
        [(? vector? d) (parse `(,quote$ ,d) tail?)] ;; ick
        [err (error 'parse "Unknown form ~a" err)])))
  (values expr open prim-fallbacks))
#;(trace parse)
(define (unparse e)
  (match e
    [(or (var _ _ x) (datum _ _ x) (primr _ _ x _)) x]
    [(app _ _ e es) (map unparse (cons e es))]
    [(lam _ _ xs body) `(λ ,xs ,(unparse body))]
    [(ife _ _ g t e) `(if ,(unparse g) ,(unparse t) ,(unparse e))]
    [(st! _ _ x e) `(set! ,x ,(unparse e))]
    [(lrc _ _ xs es body) `(letrec ,(map list xs (map unparse es)) ,(unparse body))]
    [_ (error 'unparse "Bad exp ~a" e)]))