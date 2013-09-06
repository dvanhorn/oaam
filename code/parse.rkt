#lang racket
(provide parse parse-prog unparse)
(require "ast.rkt" "primitives.rkt" "data.rkt" "macros.rkt" "tcon.rkt"
         "notation.rkt"
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
          [`(set! ,x ,e) (st! (fresh-label!) (opaque-box #f) (rename x) (parse e))]
          [`(letrec () . ,s) (parse-seq s)]
          [`(letrec ((,xs ,es) ...) . ,s)
           (define-values (xs-id ρ) (fresh-xs xs))
           (lrc (fresh-label!) (opaque-box #f) xs-id (map (parse_ ρ) es) (parse-seq s ρ))]
          [`(lambda (,xs ...) . ,s)
           (define-values (xs-id ρ) (fresh-xs xs))
           (lam (fresh-label!) (opaque-box #f) xs-id (parse-seq s ρ))]
          [`(lambda (,xs ... . ,rest) . ,s)
           (define-values (xs-id ρ) (fresh-xs xs))
           (define r-id (fresh-variable! rest))
           (rlm (fresh-label!) (opaque-box #f) xs-id r-id (parse-seq s (hash-set ρ rest r-id)))]
          [`(lambda ,x . ,s)
           (define x-id (fresh-variable! x))
           (rlm (fresh-label!) (opaque-box #f) '() x-id (parse-seq s (hash-set ρ x x-id)))]
          [`(if ,e0 ,e1 ,e2)
           (ife (fresh-label!) (opaque-box #f) (parse e0) (parse e1) (parse e2))]
          [`(if ,g ,t)
           (printf "Warning: If without else: ~a~%" sexp)
           (parse-core `(if ,g ,t (,void$)))]
          [`(let/cc ,x ,e)
           (define x-id (fresh-variable! x))
           (lcc (fresh-label!) (opaque-box #f) x-id (parse* e (hash-set ρ x x-id)))]
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          ;; Continuation marks forms
          [`(test (,(? symbol? Rs) ...) ,t ,e)
           (tst (fresh-label!) (opaque-box #f) (list->set Rs) (parse t) (parse e))]
          [`(grant (,(? symbol? Rs) ...) ,e)
           (grt (fresh-label!) (opaque-box #f) (list->set Rs) (parse e))]
          ['(fail) (fal (fresh-label!) (opaque-box #f))]
          [`(frame (,(? symbol? Rs) ...) ,e)
           (frm (fresh-label!) (opaque-box #f) (list->set Rs) (parse e))]
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          ;; Contract monitoring forms
          [`(mon (quote ,(? symbol? pℓ)) (quote ,(? symbol? nℓ)) (quote ,(? symbol? cℓ)) ,s ,e)
           (mon (fresh-label!) (opaque-box #f) (fresh-label!) pℓ nℓ cℓ (parse-scon s) (parse e))]
          [`(tmon (quote ,(? symbol? pℓ)) (quote ,(? symbol? nℓ)) (quote ,(? symbol? cℓ)) ,s ,t ,e)
           (tmon (fresh-label!) (opaque-box #f) (fresh-label!) pℓ nℓ cℓ (parse-scon s) (parse-tcon t) (parse e))]
          ;; End contract monitoring forms
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          [`(,(or 'lambda 'if 'letrec 'set!
                  #;for-continuation-marks
                  'test 'grant 'fail 'frame) . ,rest)
           (error 'parse-core "Ill-formed core form ~a" sexp)]
          [`(,(== kwote) ,d) (datum (fresh-label!) (opaque-box ∅) d)]
          [`(,(== define-ctx) . ,forms) (parse-seq forms)]
          [`(,s . ,es) (=> fail)
           (match (hash-ref macro-env s #f)
             [#f (fail)]
             [tf (parse (tf sexp))])]
          [`(,e . ,es)
           (app (fresh-label!) (opaque-box #f) (fresh-label!) (parse e) (map parse es))]
          [err (error 'parse-core "Wat ~a" err)]))

      (define (rassoc f2 f f1 if-empty lst)
        (let loop ([lst lst])
         (match lst
           ['() if-empty]
           [(list c) (f1 (f c))]
           [(cons s ss) (f2 (f s) (loop ss))])))

      (define (parse-scon s)
        (match s
          [`(cons/c ,sa ,sd) (consc (fresh-label!) (opaque-box #f) (parse-scon sa) (parse-scon sd))]
          [`(and/c ,ss ...)
           (rassoc (λ (s₀ s₁) (andc (fresh-label!) (opaque-box #f) s₀ s₁)) parse-scon values anyc ss)]
          [`(or/c ,ss ...)
           (unless (let check-h/o ([ss ss])
                        (match ss
                          [(or (list) (list _)) #t]
                          [(cons (or `(-> ,_ : ,_ ,_)
                                     `(-> ,_ ,_)) ps) #f]
                          [_ #t]))
             (error 'parse "Expected higher-order component of disjunction contract in far right ~a" s))
           (rassoc (λ (s₀ s₁) (orc (fresh-label!) (opaque-box #f) s₀ s₁)) parse-scon values nonec ss)]
          [`any anyc]
          [`none nonec]
          [(or `(,(or '-> '→) (quote ,(? symbol? name)) : ,sns ,sp)
               `((quote ,(? symbol? name)) : ,sns ... ,(or '-> '→) ,sp))
           (arrc (fresh-label!) (opaque-box #f) name (map parse-scon sns) (parse-scon sp))]
          [(or `(-> ,sns ,sp)
               `(,sns ... ,(or '→ '->) ,sp))
           (arrc (fresh-label!) (opaque-box #f) #f (map parse-scon sns) (parse-scon sp))]
          [e (fltc (fresh-label!) (opaque-box #f) (parse e))]))

      (define (parse-tcon t)
        (match t
          [`(,(or 'seq '·) ,ts ...) (rassoc (λ (T₀ T₁) (·e (opaque-box #f) (fresh-label!) T₀ T₁)) parse-tcon values ε ts)]
          ;; Use lists here since we still have to evaluate all the way down,
          ;; given expressions in patterns.
          [`(,(or '∪ 'or) ,ts ...) (tore (opaque-box #f) (fresh-label!) (map parse-tcon ts))]
          [`(,(or '∩ 'and) ,ts ...) (tande (opaque-box #f) (fresh-label!) (map parse-tcon ts))]
          ['... (tande (opaque-box ∅) (fresh-label!) '())]
          [(or 'ε 'empty) εe]
          [`(,(or 'kl 'star '*) ,t) (kle (opaque-box #f) (fresh-label!) (parse-tcon t))]
          [`(,(or 'not '¬) ,t) (¬e (opaque-box #f) (fresh-label!) (parse-tcon t))]
          [`(,(or 'dseq 'bind) ,pat ,t) (〈binde〉 (opaque-box #f) (fresh-label!) (parse-pat pat) (parse-tcon t))]
          [pat (parse-pat pat)]))

      (define (pcons pa pd)
        (constructede (opaque-box #f) (fresh-label!) 'cons (list pa pd)))
      (define (parse-pat pat)
        (match pat
          [`(,(and kind (or 'call 'ret)) ,nf ,args ...)
           (constructede (opaque-box #f) (fresh-label!) kind (map parse-pat (cons nf args)))]
          [`(!call . ,rest) (!pate (opaque-box #f) (fresh-label!) (parse-pat `(call . ,rest)))]
          [`(!ret . ,rest)  (!pate (opaque-box #f) (fresh-label!) (parse-pat `(ret  . ,rest)))]
          [`(,(or 'not '! '¬) ,p) (!pate (opaque-box #f) (fresh-label!) (parse-pat p))]
          ['_ Anye]
          [`(label ,ℓ) (labele (opaque-box ∅) (fresh-label!) ℓ)]
          [`($ ,(? symbol? x)) ($e (opaque-box ∅) (fresh-label!) x)]
          [`(? ,(? symbol? x)) (□e (opaque-box ∅) (fresh-label!) x)]
          [`(cons ,pa ,pd) (pcons (parse-pat pa) (parse-pat pd))]
          [`(list ,ps ...)
           (define dnil (datum (fresh-label!) (opaque-box ∅) '()))
           (rassoc pcons parse-pat (λ (p) (pcons p dnil)) dnil ps)]
          ;; evaluate the expression at monitor creation time and create temporal contract with value.
          [e (parse e)]))

      (match sexp
        [`(,(== special) . ,s) (primr (fresh-label!) (opaque-box ∅) s)]
        [`((,(== special) . ,s) . ,es)
         (if (primitive? s)
             (app (fresh-label!)
                  (opaque-box #f)
                  (fresh-label!)
                  (primr (fresh-label!) s)
                  (map parse es))
             (parse-core (cons s es)))]
        [`(,e . ,es)
         (cond [(hash-has-key? ρ e)
                (define e* (rename e))
                (app (fresh-label!)
                     (opaque-box #f)
                     (fresh-label!)
                     (var (fresh-label!) (opaque-box (set e*)) e*)
                     (map parse es))]               
               [else (parse-core sexp)])]
        [(? symbol? s)
         (define (mkvar)
           (define s* (rename s))
           (var (fresh-label!) (opaque-box (set s*)) s*))
         (cond [(hash-has-key? ρ s) (mkvar)]
               [(primitive? s) (primr (fresh-label!) (opaque-box ∅) s)]
               [(hash-ref prim-constants s #f) =>
                (λ (d) (datum (fresh-label!) (opaque-box ∅) d))]
               [else (mkvar)])] ;; will error
        [(? atomic? d) (datum (fresh-label!) (opaque-box ∅) d)]
        [(? vector? d) (parse `(,quote$ ,d))] ;; ick
        [err (error 'parse "Unknown form ~a" err)])))
  (values expr open))

#;
(trace parse)
(define (unparse e)
  (match e
    [(or (var _ _ x) (datum _ _ x) (primr _ _ x)) x]
    [(app _ _ _ e es) (map unparse (cons e es))]
    [(lam _ _ xs body) `(λ ,xs ,(unparse body))]
    [(ife _ _ g t e) `(if ,(unparse g) ,(unparse t) ,(unparse e))]
    [(st! _ _ x e) `(set! ,x ,(unparse e))]
    [(lrc _ _ xs es body) `(letrec ,(map list xs (map unparse es)) ,(unparse body))]
    [_ (error 'unparse "Bad exp ~a" e)]))