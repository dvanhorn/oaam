#lang racket/base

(require (for-syntax syntax/parse syntax/id-table racket/base racket/match
                     racket/dict racket/syntax racket/list)
         #;racket/match (except-in racket/match match match*)
         "notation.rkt"
         racket/stxparam)
(provide mk-syntax-parameters
         in-scope-of-extras initialize-targets match-function
         st-targets al-targets cr-targets av-targets empty-heap
         tλ tapp called-function
         (for-syntax
          target target-param target-kw target-initializer ;;(struct-out target)
          get-targets get-stalcr get-stcr get-st get-cr #;kw<=? target<=?
          kw-in-target remove-kw-target called-fn-target
          apply-transformer σ-target
          formals actuals comp-clauses
          exn-wrap))

(define-for-syntax (exn-wrap stx syn)
#;
  syn
  
  (quasisyntax/loc syn (with-handlers ([exn:fail:contract:arity?
                     (λ (ex) (error 'do "Problem in ~a~%as ~a~%~a" '#,stx '#,syn ex))])
      #,syn)))

(define-syntax-rule (mk-syntax-parameters id ...)
  (begin (define-syntax-parameter id #f) ... (provide id ...)))

(mk-syntax-parameters bind-join
                      bind-get bind-force bind-delay
                      bind bind-rest bind-rest-apply
                      ;; 'alloc' a-la AAM, but with less context. More k-CFA-like.
                      make-var-contour
                      ;; single-threaded parameter necessary for semantics
                      target-σ)
(define-syntax-parameter in-scope-of-extras (syntax-rules () [(_ ids body ...) (begin body ...)]))
(define-syntax-parameter called-function (λ _ #'#f))
(define-syntax-parameter empty-heap (make-rename-transformer #'hash))

(define-syntax initialize-σ (syntax-rules () [(_ e) e]))

;; Bind the value of the matched function only if that target is needed.
(define-simple-macro* (match-function e [pat rhs ...] ...)
  #,(if (kw-in-target '#:called-function (syntax-parameter-value #'av-targets))
        #'(let ([f e])
            (syntax-parameterize ([called-function (make-rename-transformer #'f)])
              (match f [pat rhs ...] ...)))
        #'(match e [pat rhs ...] ...)))

#|
There are several different classes of bindings that the framework maintains.
* single-threaded - these bindings are always accumulated through loops.
* allocation-threaded - these bindings are consistently available, but only
accumulated in forms that specify #:extra. (XXX: general enough? Might need to extend the filtering)
* carried - Behave like allocation-threaded, but must be returned as extra values in some forms.
* available - Not accumulated, but maintained through lifting.

The semantics of the language depends on the heap being single-threaded.
Each accumulator is given a chance to initialize. In the bodies of lifted functions (λ% λP lift-do)
and do. do will not initialize an accumulator in the static extent of another do.
|#

;; Targets must be syntax-parameters that also are paired with an identifier
;; of its initializer form. Targets have associated keywords for forms to give
;; specific bindings. We need this especially for naming the store.
(define-syntax-parameter st-targets '())
(define-syntax-parameter al-targets '())
(define-syntax-parameter cr-targets '())
(define-syntax-parameter av-targets '())

;; A Target is a (target Syntax-Parameter Keyword (U Identifier Transformer))
;; where the identifier is bound to a function/macro that expects an optional
;; #:given e
;; followed by body:expr ...+
;; this is to "initialize" a binding in the beginning of a managed function or
;; do body. A do will not initialize a binding if it in the static extent of a managed function
;; or another do form.

;; Wrap initializers in sorted target order.
(begin-for-syntax
 (struct target (param kw initializer))
 (define σ-target (target #'target-σ '#:σ (make-rename-transformer #'initialize-σ)))
 (define called-fn-target (target #'called-function '#:called-function (syntax-rules () [(_ e) e])))
 (define (kw<=? s t)
   (string<=? (keyword->string s) (keyword->string t)))

 (define (target<=? s t) (kw<=? (target-kw s) (target-kw t)))

 (define (get-targets)
   (sort (append (syntax-parameter-value #'st-targets)
                 (syntax-parameter-value #'al-targets)
                 (syntax-parameter-value #'av-targets)
                 (syntax-parameter-value #'cr-targets))
         target<=?))

 (define (get-stalcr)
   (sort (append (syntax-parameter-value #'st-targets)
                 (syntax-parameter-value #'al-targets)
                 (syntax-parameter-value #'cr-targets))
         target<=?))

 (define (get-st) (sort (syntax-parameter-value #'st-targets) target<=?))
 (define (get-cr) (sort (syntax-parameter-value #'cr-targets) target<=?))

 (define (get-stcr)
   (sort (append (syntax-parameter-value #'st-targets)
                 (syntax-parameter-value #'cr-targets))
         target<=?))

 (define (kw-in-target kw targs)
   (for/or ([t (in-list targs)])
     (eq? kw (target-kw t))))

 ;; expected INVARIANT: Can't have duplicate keywords in targets
 (define (remove-kw-target kw targs)
   (let loop ([targs targs])
     (match targs
       ['() '()]
       [(cons (and t (target _ kw* _)) targs)
        (if (eq? kw kw*)
            targs
            (cons t (loop targs)))])))

 (define (apply-transformer f stx)
   (cond [(procedure? f) (f stx)]
         [else
          (define target
            (cond [(rename-transformer? f) (rename-transformer-target f)]
                  [(identifier? f) f]
                  [else (error 'apply-transformer "Bad transformer ~a" f)]))
          #`(#,target . #,(cdr (syntax-e stx)))]))

 (define (no-duplicates? x)
   (define h (make-hash))
   (not (for/or ([v (in-list x)])
          (begin0 (hash-has-key? h v)
                  (hash-set! h v #t)))))

 (struct err-pred (f msg)
         #:property prop:procedure (struct-field-index f))
 (define id-err (err-pred identifier? "Expected an identifier after keyword"))
 (define expr-err (err-pred (syntax-parser [e:expr #t] [_ #f])
                            "Expected an expression after keyword"))

 ;; Syntax classes for naming targets with keywords
 ;; all : List[Target]
 (define-splicing-syntax-class (kw-stx all pred)
   #:attributes (kw after)
   (pattern (~seq k:keyword a)
            #:fail-unless (pred #'a)
            (err-pred-msg pred)
            #:do [(define bind?
                    (for/or ([t (in-list all)])
                      (eq? (target-kw t) (syntax-e #'k))))]
            #:attr kw (and bind? (syntax-e #'k))
            #:attr after (and bind? #'a)))

 (define (sort-by-kw zipped)
   (map second (sort zipped kw<=? #:key first)))

 (define-syntax-class (formals all drop-unused-cr?)
   #:attributes ((kw-ids 1) (ids 1) (kws 1))
   ;; Target specified (in order)
   (pattern ((~or (~var k (kw-stx all id-err)) ids:id) ...)
            #:do [(define good-kw (filter values (attribute k.kw)))
                  (define good-ids (filter values (attribute k.after)))]
            #:fail-unless (no-duplicates? (attribute k.kw))
            "Cannot specify the same keyword twice."
            #:do [(define appended (append good-ids (attribute ids)))]
            #:fail-when (check-duplicate-identifier appended)
            (format "Duplicate identifiers ~a" appended)
            #:do [(define unspec-bind
                    ;; Identifiers that need binding, but not explicitly given
                    (for*/list ([t (in-list all)]
                                [kw (in-value (target-kw t))]
                                #:unless (or (memq kw good-kw)
                                             (and drop-unused-cr?
                                                  (memf (λ (t) (eq? kw (target-kw t)))
                                                        (syntax-parameter-value #'cr-targets)))))
                      (define temp (generate-temporary (target-param t)))
                      (list kw temp)))]
            #:with (kw-ids ...)
            (sort-by-kw (append (map list good-kw good-ids) unspec-bind))
            #:attr (kws 1) (sort good-kw kw<=?)))
 
 (define-splicing-syntax-class (actuals all)
   #:attributes ((kw-exprs 1) (exprs 1))
   (pattern (~seq (~or (~var k (kw-stx all expr-err)) e:expr) ...)
            #:do [(define good-kw (filter values (attribute k.kw)))
                  (define good-exprs (filter values (attribute k.after)))]
            #:fail-unless (no-duplicates? (attribute k.kw))
            "Cannot specify the same keyword twice."
            #:attr (kw-exprs 1) (map cons good-kw good-exprs)
            #:with (exprs ...) #'(e ...)))

 ;; Used in do, but not do-specific
 (define-splicing-syntax-class comp-clauses
   #:attributes ((guards 1))
   #:description "Clause forms allowed in for loops"
   (pattern (~and (~seq (~or [_:id _:expr]
                             [(_:id ...) _:expr]
                             (~seq #:when _:expr)
                             (~seq #:unless _:expr)
                             (~seq #:break _:expr)
                             (~seq #:final _:expr)) ...+)
                  (~seq guards ...)))))

(define-syntax (tλ stx)
  (define all (get-targets))
  ;; If keyword in the list of targets' keywords, then bind.
  ;; otherwise, drop the binding.
  (syntax-parse stx
    [(_ (~var f (formals all #f)) . body)
     ;; Don't use the parameter's names since then they get rebound
     ;; by λ
     (with-syntax ([(accs ...) (map target-param all)])
       (quasisyntax/loc stx
         (λ (f.kw-ids ... f.ids ...)
            (syntax-parameterize ([accs (make-rename-transformer #'f.kw-ids)] ...
                                  [initialized? #t])
              . body))))]))

;; Apply a tλ
(define-syntax (tapp stx)
  (define all (get-targets))
  (syntax-parse stx
    [(_ lifted (~var a (actuals all)))
     ;; Pass all accumulators in sorted order, replacing with specified
     ;; expressions when keywords present.
     (define explicit (attribute a.kw-exprs))
     (with-syntax ([(accs ...)
                    (for/list ([t (in-list all)])
                      (or (dict-ref explicit (target-kw t) #f)
                          (target-param t)))])
       (exn-wrap stx (syntax/loc stx (lifted accs ... a.exprs ...))))]))

(define-syntax-parameter initialized? #f)
(define-syntax (initialize-targets stx)
  (define all (get-targets))
  (syntax-case stx ()
    [(_ e ...)
     (if (syntax-parameter-value #'initialized?)
         #'(let () e ...)
         (for/fold ([out #'(syntax-parameterize ([initialized? #t])
                             e ...)])
             ([t (in-list (reverse all))])
           (apply-transformer (target-initializer t)
                              #`(initialize-targets #,out))))]))
