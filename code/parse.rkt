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
          [`(let/cc ,x ,e)
           (define x-id (fresh-variable! x))
           (lcc (fresh-label!) x-id (parse* e (hash-set ρ x x-id)))]
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          ;; Continuation marks forms
          [`(test (,(? symbol? Rs) ...) ,t ,e)
           (tst (fresh-label!) (list->set Rs) (parse t) (parse e))]
          [`(grant (,(? symbol? Rs) ...) ,e)
           (grt (fresh-label!) (list->set Rs) (parse e))]
          ['(fail) (fal (fresh-label!))]
          [`(frame (,(? symbol? Rs) ...) ,e)
           (frm (fresh-label!) (list->set Rs) (parse e))]
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          ;; Contract monitoring forms
          [`(mon (quote ,(? symbol? pℓ)) (quote ,(? symbol? nℓ)) (quote ,(? symbol? cℓ)) ,s ,e)
           (mon (fresh-label!) pℓ nℓ cℓ (parse-scon s) (parse e))]
          [`(tmon (quote ,(? symbol? pℓ)) (quote ,(? symbol? nℓ)) (quote ,(? symbol? cℓ)) ,s ,t ,e)
           (tmon (fresh-label!) pℓ nℓ cℓ (parse-scon s) (parse-tcon t) (parse e))]
          ;; End contract monitoring forms
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          [`(,(or 'lambda 'if 'letrec 'set!
                  #;for-continuation-marks
                  'test 'grant 'fail 'frame) . ,rest)
           (error 'parse-core "Ill-formed core form ~a" sexp)]
          [`(,(== kwote) ,d) (datum (fresh-label!) d)]
          [`(,(== define-ctx) . ,forms) (parse-seq forms)]
          [`(,s . ,es) (=> fail)
           (match (hash-ref macro-env s #f)
             [#f (fail)]
             [tf (parse (tf sexp))])]
          [`(,e . ,es)
           (app (fresh-label!) (parse e) (map parse es))]
          [err (error 'parse-core "Wat ~a" err)]))

      (define (rassoc f2 f if-empty lst)
        (let loop ([lst lst])
         (match lst
           ['() if-empty]
           [(list c) (f c)]
           [(cons s ss) (f2 (f s) (loop ss))])))

      (define (parse-scon s)
        (match s
          [`(cons/c ,sa ,sd) (consc (fresh-label!) (parse-scon sa) (parse-scon sd))]
          [`(and/c ,ss ...) (rassoc (λ (s₀ s₁) (andc (fresh-label!) s₀ s₁)) parse-scon anyc ss)]
          [`(or/c ,ss ...)
           (unless (let check-h/o ([ss ss])
                        (match ss
                          [(or (list) (list _)) #t]
                          [(cons (or `(-> ,_ : ,_ ,_)
                                     `(-> ,_ ,_)) ps) #f]
                          [_ #t]))
             (error 'parse "Expected higher-order component of disjunction contract in far right ~a" s))
           (rassoc (λ (s₀ s₁) (orc (fresh-label!) s₀ s₁)) parse-scon nonec ss)]
          [`any anyc]
          [`none nonec]
          [(or `(,(or '-> '→) (quote ,(? symbol? name)) : ,sns ,sp)
               `((quote ,(? symbol? name)) : ,sns ... ,(or '-> '→) ,sp))
           (arrc (fresh-label!) name (map parse-scon sns) (parse-scon sp))]
          [(or `(-> ,sns ,sp)
               `(,sns ... ,(or '→ '->) ,sp))
           (arrc (fresh-label!) #f (map parse-scon sns) (parse-scon sp))]
          [e (fltc (fresh-label!) (parse e))]))

      (define (parse-tcon t)
        (match t
          [`(,(or 'seq '·) ,ts ...) (rassoc · parse-tcon ε ts)]
          [`(,(or '∪ 'or) ,ts ...) (tor (for/set ([t (in-list ts)]) (parse-tcon t)))]
          [`(,(or '∩ 'and) ,ts ...) (tand (for/set ([t (in-list ts)]) (parse-tcon t)))]
          [(or 'ε 'empty) ε]
          [`(,(or 'kl 'star) ,t) (kl (parse-tcon t))]
          [`(,(or 'not '¬) ,t) (¬ (parse-tcon t))]
          [`(,(or 'dseq 'bind) ,pat ,t) (bind (parse-pat pat) (parse-tcon t))]
          ['... (tand ∅)]
          [pat (parse-pat pat)]))

      (define (parse-pat pat)
        (match pat
          [`(call ,nf ,args ...) (call (parse-pat nf) (map parse-pat args))]
          [`(!call ,nf ,args ...) (!call (parse-pat nf) (map parse-pat args))]
          [`(ret ,nf ,vp) (ret (parse-pat nf) (parse-pat vp))]
          [`(!ret ,nf ,vp) (!ret (parse-pat nf) (parse-pat vp))]
          ['_ Any]
          [`(quote ,ℓ) (label ℓ)]
          [`($ ,(? symbol? x)) ($ x)]
          [`(? ,(? symbol? x)) (□ x)]
          [err (error 'parse-pat "Wuh ~a" err)]))

      (match sexp
        [`(,(== special) . ,s) (primr (fresh-label!) s)]
        [`((,(== special) . ,s) . ,es)
         (if (primitive? s)
             (app (fresh-label!)
                  (primr (fresh-label!) s)
                  (map parse es))
             (parse-core (cons s es)))]
        [`(,e . ,es)
         (cond [(hash-has-key? ρ e)
                (app (fresh-label!)
                     (var (fresh-label!) (rename e))
                     (map parse es))]               
               [else (parse-core sexp)])]
        [(? symbol? s)
         (define (mkvar) (var (fresh-label!) (rename s)))
         (cond [(hash-has-key? ρ s) (mkvar)]
               [(primitive? s) (primr (fresh-label!) s)]
               [(hash-ref prim-constants s #f) =>
                (λ (d) (datum (fresh-label!) d))]
               [else (mkvar)])] ;; will error
        [(? atomic? d) (datum (fresh-label!) d)]
        [(? vector? d) (parse `(,quote$ ,d))] ;; ick
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