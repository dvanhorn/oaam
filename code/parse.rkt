#lang racket
(require "ast.rkt" "primitives.rkt" "data.rkt" "macros.rkt" "egal-box.rkt"
         "notation.rkt"
         (for-syntax syntax/parse)
         racket/mpair racket/stxparam racket/splicing
         racket/trace)
(provide parse parse-prog with-parse add-lib
         unparse
         internal-apply$
         ext-ctx get-ctx top-ctx
         fresh-label! fresh-variable!
         register-fn register-datum)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser
(define prim-fallbacks #f)
(define (reset-prim-fallbacks!) (set! prim-fallbacks (make-hasheq)))
(define (simple-fresh-label! ctx new?) (gensym))
(define (simple-fresh-variable! x ctx) (gensym x))

;; Some analyses require extra/different information attached to ASTs or
;; change the function/constant registration callbacks. In order to make
;; analysis construction composable, we make these callbacks parameters.

(define-syntax-parameter parse-prog #f)
(define-syntax-parameter parse #f)
(define-syntax-parameter add-lib #f)
(define-syntax-parameter top-ctx (λ _ #'#f))
(define-syntax-parameter ext-ctx (syntax-rules () [(_ label ctx kind) #f]))
(define-syntax-parameter get-ctx (syntax-rules () [(_ ctx) #f]))
(define-syntax-parameter register-fn (make-rename-transformer #'void))
(define-syntax-parameter register-datum (make-rename-transformer #'void))
(define-syntax-parameter fresh-label! (make-rename-transformer #'simple-fresh-label!))
(define-syntax-parameter fresh-variable! (make-rename-transformer #'simple-fresh-variable!))

(define-syntax-rule (with-parse . rest-forms)
  (...
  (begin
    (define (custom-parse-prog sexp)
      (reset-prim-fallbacks!)
      (custom-parse (cons define-ctx sexp)))
    #;(trace parse-prog)

    (define (custom-parse sexp #:fresh-variable! [pfresh-variable! #f])
      (define -fresh-variable! (or pfresh-variable! fresh-variable!))
      ;; in order for the renaming to work on open programs, we not only have to return
      ;; the renamed program, but also a map from free variables to their new names.
      (define open (make-hasheq))
      (define prims-used (make-hasheq))
      (define ((new-free x ctx))
        (match (hash-ref open x #f)
          [#f (define x-id (-fresh-variable! x ctx))
              (hash-set! open x x-id)
              x-id]
          [s s]))
      (define expr
        (let parse* ([sexp sexp]
                     [tail? #t]
                     [ctx top-ctx]
                     [ρ (hasheq)])
          (define (parse sexp tail?) (parse* sexp tail? ctx ρ))
          (define ((parse_ tail? ctx [ρ ρ]) sexp) (parse* sexp tail? ctx ρ))
          (define (rename x) (hash-ref ρ x (new-free x ctx)))
          (define (parse-seq s tail? ctx [ρ ρ]) (parse* (define-ctx-tf s) tail? ctx ρ))
          (define (ext-ctx* label kind) (ext-ctx label ctx kind))
          (define (fresh-label*) (fresh-label! ctx #f))
          (define (fresh-variable* x) (-fresh-variable! x ctx))
          (define (fresh-xs xs ctx)
            (define xs-id (map fresh-variable* xs))
            (values xs-id
                    (for/fold ([ρ ρ]) ([x xs] [x-id xs-id]) (hash-set ρ x x-id))))
          (define-simple-macro* (define/ctx (ctx*:id label:id) kind:id)
            (begin
              (define ctx* (ext-ctx* (fresh-label! ctx #,(eq? (syntax-e #'kind) 'λ)) 'kind))
              (define label (get-ctx ctx*))))
          (define (mk-primr tail? ctx which)
            (define b (hash-ref! prim-fallbacks which (λ () (ebox #f)) ))
            (define/ctx (ctx* ℓ) primref)
            (primr (fresh-label! ctx #f) tail? which b))
          (define (parse-core sexp)
            (match sexp
              [`(set! ,x ,e)
               (define/ctx (ctx* ℓ) set!) 
               (st! ℓ tail? (rename x) (parse* e #f ctx* ρ))]
              [`(letrec () . ,s) (parse-seq s tail? ctx)]
              [`(letrec ((,xs ,es) ...) . ,s)
               (define/ctx (ctx* ℓ) letrec)
               (define-values (xs-id ρ) (fresh-xs xs ctx*))
               (lrc ℓ tail? xs-id (map (parse_ #f ctx* ρ) es)
                    (parse-seq s tail? ctx* ρ))]
              [`(lambda (,xs ...) . ,s)
               (define/ctx (ctx* ℓ) λ)
               (define-values (xs-id ρ) (fresh-xs xs ctx*))
               (define fn (lam ℓ tail? xs-id (parse-seq s #t ctx* ρ)))
               (register-fn fn)
               fn]
              [`(lambda (,xs ... . ,rest) . ,s)
               (define/ctx (ctx* ℓ) λ)
               (define-values (xs-id ρ) (fresh-xs xs ctx*))
               (define r-id (-fresh-variable! rest ctx*))
               (define fn (rlm ℓ tail? xs-id r-id (parse-seq s #t ctx* (hash-set ρ rest r-id))))
               (register-fn fn)
               fn]
              [`(lambda ,x . ,s)
               (define/ctx (ctx* ℓ) λ)
               (define x-id (-fresh-variable! x ctx*))
               (define fn (rlm ℓ tail? '() x-id (parse-seq s #t ctx* (hash-set ρ x x-id))))
               (register-fn fn)
               fn]
              ;; Specialize let-like lambda
              [`((,(or 'lambda `(,(== special) . lambda)) () . ,body))
               (parse-seq body tail? ctx)]
              [(or `((,(or 'lambda `(,(== special) . lambda)) (,xs ...) . ,body) . ,es)
                   `(core-let ([,xs ,es] ...) . ,body))
               (define/ctx (ctx* ℓ) let)
               (define-values (xs-id ρ*) (fresh-xs xs ctx*))
               (unless (list? es)
                 (error 'parse "Bad let ~a" sexp))
               (lte ℓ tail? xs-id (map (parse_ #f ctx) es) (parse-seq body tail? ctx* ρ*))]
              [`(if ,e0 ,e1 ,e2)
               (define/ctx (ctx* ℓ) if)
               (ife ℓ tail? (parse* e0 #f ctx* ρ) (parse e1 tail?) (parse e2 tail?))]
              [`(if ,g ,t)
               (printf "Warning: If without else: ~a~%" sexp)
               (parse-core `(if ,g ,t (,void$)))]
              [`(let/cc ,x ,e)
               (define/ctx (ctx* ℓ) let/cc)
               (define x-id (fresh-variable* x))
               (lcc ℓ tail? x-id (parse* e tail? ctx* (hash-set ρ x x-id)))]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
              ;; Continuation marks forms
              [`(test (,(? symbol? Rs) ...) ,t ,e)
               (define/ctx (ctx* ℓ) test)
               (tst ℓ tail? (list->set Rs) (parse t tail?) (parse e tail?))]
              [`(grant (,(? symbol? Rs) ...) ,e)
               (define/ctx (ctx* ℓ) grant)
               (grt ℓ tail? (list->set Rs) (parse e #f))]
              ['(fail)
               (define/ctx (ctx* ℓ) fail)
               (fal ℓ tail?)]
              [`(frame (,(? symbol? Rs) ...) ,e)
               (define/ctx (ctx* ℓ) frame)
               (frm ℓ tail? (list->set Rs) (parse e #f))]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
              ;; End Continuation marks forms
              [`(,(or 'lambda 'if 'letrec 'set!
                      #;for-continuation-marks
                      'test 'grant 'fail 'frame) . ,rest)
               (error 'parse-core "Ill-formed core form ~a" sexp)]
              [`(,(== kwote) ,d)
               (define/ctx (ctx* ℓ) datum)
               (register-datum d)
               (datum ℓ tail? d)]
              [`(,(== define-ctx) . ,forms) (parse-seq forms tail? ctx)]
              [`(,s . ,es) (=> fail)
               (match (hash-ref macro-env s #f)
                 [#f (fail)]
                 [tf (parse (tf sexp) tail?)])]
              [`(,e . ,es)
               (unless (list? es)
                 (error 'parse "Bad application ~a" sexp))
               (define/ctx (ctx* ℓ) app)
               (app ℓ tail? (parse* e #f ctx* ρ) (map (parse_ #f ctx*) es))]))

          (match sexp
            [`(,(== special) . ,s) (mk-primr tail? ctx s)]
            [`((,(== special) . ,s) . ,es)
             (cond [(primitive? s)
                    (define/ctx (ctx* ℓ) app)
                    (app ℓ tail?
                         (mk-primr #f ctx* s)
                         (map (parse_ #f ctx*) es))]
                   [else (parse-core (cons s es))])]
            [`(,e . ,es)
             (cond [(hash-has-key? ρ e)
                    (define/ctx (ctx* ℓ) app)
                    (app ℓ tail?
                         (var ℓ #f (rename e))
                         (map (parse_ #f ctx*) es))]
                   [else (parse-core sexp)])]
            [(? symbol? s)
             (define (mkvar)
               (define/ctx (ctx* ℓ) var)
               (var ℓ tail? (rename s)))
             (cond [(hash-has-key? ρ s) (mkvar)]
                   [(primitive? s) (mk-primr tail? ctx s)]
                   [(hash-ref prim-constants s #f) =>
                    (λ (d)
                       (define/ctx (ctx* ℓ) datum)
                       (register-datum d)
                       (datum ℓ tail? d))]
                   [else (mkvar)])] ;; will error
            [(? atomic? d)
             (define/ctx (ctx* ℓ) datum)
             (register-datum d)
             (datum ℓ tail? d)]
            [(? vector? d) (parse `(,quote$ ,d) tail?)] ;; ick
            [err (error 'parse "Unknown form ~a" err)])))
      (values expr open prim-fallbacks))
    (splicing-syntax-parameterize
        ([parse (make-rename-transformer #'custom-parse)]
         [parse-prog (make-rename-transformer #'custom-parse-prog)])
      . rest-forms))))

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