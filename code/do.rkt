#lang racket
(require (for-syntax syntax/parse racket/syntax racket/list)
         racket/stxparam "notation.rkt" "data.rkt"
         racket/generator)
(provide do-values continue do-comp
         bind-alias bind-join-local bind-get-kont bind-push
         in-scope-of-extras match-function
         (for-syntax mk-do mk-lift-do mk-do-app listy with-do-binds))

;; Helper for building targets
(define-for-syntax (listy x) (if x (list x) '()))

(define-syntax (do-values stx)
  (syntax-parse stx
    [(_ . args)
     (define tσtcs
       (append (listy (and (syntax-parameter-value #'target-σ?) #'target-σ))
               (listy (and (syntax-parameter-value #'target-cs?) #'target-cs))
               (listy (and (syntax-parameter-value #'target-actions?) #'target-actions))))
     #`(values #,@tσtcs . args)]))
(define-syntax-rule (continue) (do-values))

(define-syntax-rule (mk-syntax-parameters id ...)
  (begin (define-syntax-parameter id #f) ... (provide id ...)))

(mk-syntax-parameters bind-join bind-join*
                      bind-alias* bind-big-alias
                      bind-get bind-force bind-delay
                      bind bind-rest bind-rest-apply make-var-contour
                      ;; do-specific
                      do lift-do do-app do-extra-values
                      ;; The called-function parameter is mostly for CFA2's fake-rebinding.
                      called-function
                      ;; Hidden accumulators and whether they should be kept
                      target-σ? target-σ target-cs? target-cs
                      top-actions? target-actions? target-actions
                      top-σ top-σ?
                      ;; Starting an action accumulation needs the representation
                      ;; of "no actions."
                      empty-actions)

(define-syntax-rule (match-function e [pat rhs ...] ...)
  (let ([f e])
    (syntax-parameterize ([called-function (make-rename-transformer #'f)])
      (match f [pat rhs ...] ...))))

;; default: do nothing to the body of a do.
(define-syntax-parameter do-body-transformer (syntax-rules () [(_ e) e]))
(provide do-body-transformer)
;; for tandem analysis. default: bind nothing
(define-syntax-parameter bind-extra
  (syntax-rules () [(_ ids body ...) (let () body ...)]))
(define-syntax-parameter bind-extra-initial
  (syntax-rules () [(_ body ...) (let () body ...)]))
(provide bind-extra bind-extra-initial)
;; regular vs pushdown. Default: regular
(define-syntax-parameter bind-push
  (syntax-rules ()
    [(_ (σ* a* bpσ l δ k) body)
     (let ([a* (make-var-contour l δ)])
       (bind-join (σ* bpσ a* (singleton k)) body))]))
(define-syntax-parameter bind-get-kont (make-rename-transformer #'bind-get))
(define-syntax-parameter bind-join-local (make-rename-transformer #'bind-join))
(define-syntax-parameter in-scope-of-extras (syntax-rules () [(_ ids body ...) (begin body ...)]))

(define-syntax-rule (bind-alias (σ* σ alias to-alias) body)
  (bind-get (res σ to-alias) (bind-join (σ* σ alias res) body)))

;; Private
(define-syntax-parameter in-do-ctx? #f)
(define-syntax-rule (with-do body ...)
  (syntax-parameterize ([in-do-ctx? #t]) body ...))

;; Sometimes we need to factor out the body of a do form. To avoid
;; code duplication, we lift to a lambda, but add in the identifiers that
;; the do form hides. Colludes with do-app.
(define-for-syntax ((mk-lift-do extras) stx)
  (syntax-parse stx
    [(_ (ids ...) . body)
     (define tσ (syntax-parameter-value #'target-σ?))
     (define tcs (syntax-parameter-value #'target-cs?))
     (define tas (syntax-parameter-value #'target-actions?))
     (define top? (syntax-parameter-value #'top-σ?))
     (define top-A? (syntax-parameter-value #'top-actions?))
     ;; Don't use the parameter's names since then they get rebound
     ;; by λ
     (with-syntax ([(top-op ...) (listy (and top? #'-top-σ))]
                   [(σ-op ...) (listy (and tσ #'-target-σ))]
                   [(cs-op ...) (listy (and tcs #'-target-cs))]
                   [(act-op ...) (listy (and tas #'-target-actions))]
                   [(extra-ids ...) (generate-temporaries extras)]
                   [(extras ...) extras])
       (quasisyntax/loc stx
         (λ (top-op ... σ-op ... cs-op ... act-op ... extra-ids ... ids ...)
            (syntax-parameterize ([top-σ (make-rename-transformer #'top-op)] ...
                                  [top-σ? #,top?]
                                  [top-actions? #,top-A?]
                                  [target-cs (make-rename-transformer #'cs-op)] ...
                                  [target-σ (make-rename-transformer #'σ-op)] ...
                                  [target-actions (make-rename-transformer #'act-op)] ...
                                  [extras (make-rename-transformer #'extra-ids)] ...
                                  [in-do-ctx? #t])
              . body))))]))

;; Apply a lifted do expression
(define-for-syntax ((mk-do-app extras) stx)
  (syntax-parse stx
    [(_ lifted . args)
     (define tσ (syntax-parameter-value #'target-σ?))
     (define tcs (syntax-parameter-value #'target-cs?))
     (define tas (syntax-parameter-value #'target-actions?))
     (define top? (syntax-parameter-value #'top-σ?))
     (with-syntax ([(top-op ...) (listy (and top? #'top-σ))]
                   [(σ-op ...) (listy (and tσ #'target-σ))]
                   [(cs-op ...) (listy (and tcs #'target-cs))]
                   [(act-op ...) (listy (and tas #'target-actions))]
                   [(extras ...) extras])
       (syntax/loc stx
         (lifted top-op ... σ-op ... cs-op ... act-op ... extras ... . args)))]))

(begin-for-syntax
 (define-syntax with-do-binds
   (syntax-rules ()
     [(_ extra body ...)
      (with-syntax ([(extra (... ...))
                     (let ([xn (syntax-parameter-value #'do-extra-values)])
                       (if xn
                           (generate-temporaries (make-list xn 'ignore))
                           '()))])
        body ...)])))

;; Compose do forms
(define-syntax (do-comp stx)
  (syntax-parse stx
    [(_ e) #'e]
    [(_ (~optional (~seq #:bind (σ:id res:id ...))) e es ...)
     (define tσ (syntax-parameter-value #'target-σ?))
     (define tcs (syntax-parameter-value #'target-cs?))
     (define tas (syntax-parameter-value #'target-actions?))
     (define extra (syntax-parameter-value #'do-extra-values))
     (with-syntax ([(σ-id ...) (listy (and tσ (or (attribute σ) (generate-temporary #'σ))))]
                   [(cs-id ...) (listy (and tcs (generate-temporary #'cs)))]
                   [(act-id ...) (listy (and tas (generate-temporary #'actions)))]
                   [(bind ...) (if (attribute res)
                                   #'(res ...)
                                   (with-do-binds extra #'(extra ...)))])
       (if (or tσ tcs tas (attribute res))
           #`(with-handlers ([exn:fail:contract:arity?
                              (λ (exn) (raise-syntax-error #f (format "Bad extra ~a" exn) #'#,stx))])
               (let-values ([(σ-id ... cs-id ... act-id ... bind ...)
                             (syntax-parameterize
                                 ([do-extra-values (length (syntax->list #'(bind ...)))])
                               e)])
                 (syntax-parameterize ([target-σ (make-rename-transformer #'σ-id)] ...
                                       [target-cs (make-rename-transformer #'cs-id)] ...
                                       [target-actions (make-rename-transformer #'act-id)] ...)
                   (do-comp es ...))))
           #'(begin e es ...)))]))

(define-for-syntax ((mk-do σ-∆s? global-σ? generators?) stx)
  ;; Construct the values tuple given the previously bound σ and cs
  (define in-do? (syntax-parameter-value #'in-do-ctx?))
  (define tσ (syntax-parameter-value #'target-σ?))
  (define tcs (syntax-parameter-value #'target-cs?))
  (define tas (syntax-parameter-value #'target-actions?))
  (define top? (syntax-parameter-value #'top-σ?))
  (define gen-wrap
    (cond [(or in-do? (not generators?)) values]
          [(and global-σ? (not σ-∆s?)) (λ (stx) #`(begin #,stx 'done))]
          [else (λ (stx) #`(begin (yield #,stx) 'done))]))
  (define add-void? (and global-σ? (not σ-∆s?) (not tas)
                         (let ([xn (syntax-parameter-value #'do-extra-values)])
                           (if xn (zero? xn) #t))))
  (define tσtcs
    (append (listy (and tσ #'target-σ))
            (listy (and tcs #'target-cs))
            (listy (and tas #'target-actions))))

  (define (init-target-actions body)
    (cond [(and (not (syntax-parameter-value #'top-actions?))
                (not in-do?) tas)
           (define actions-id (generate-temporary #'hidden-actions))
           #`(let ([#,actions-id (empty-actions)])               
               (syntax-parameterize ([target-actions (make-rename-transformer #'#,actions-id)]
                                     [top-actions? #t])
                 #,body))]
          [else body]))

  (define (init-target-cs body)
    (cond [(and (not in-do?) tcs)
           #`(let ([cs ∅])
               (syntax-parameterize ([target-cs (make-rename-transformer #'cs)])
                 #,body))]
          [else body]))

  ;; If the top level store is not already installed by λ%, and we are
  ;; not in the middle of constructing a do form, create a hidden binding
  ;; to track the top level store. While we're at it, create the target store
  ;; binding (in σ-∆s it starts off at '())
  (define (init-top-σ tσ body)
    (cond [(or top? in-do? (and (not σ-∆s?) global-σ?)) body]
          [(and σ-∆s? global-σ?)
           #`(let ([#,tσ '()])
               (syntax-parameterize ([target-σ (make-rename-transformer #'#,tσ)])
                 #,body))]
          [else
           (define σ-id (generate-temporary #'hidden-top))
           #`(let ([#,σ-id #,tσ]
                   #,(if σ-∆s? #`[#,tσ '()] #`[#,tσ #,tσ]))
               (syntax-parameterize ([top-σ (make-rename-transformer #'#,σ-id)]
                                     [target-σ (make-rename-transformer #'#,tσ)]
                                     [top-σ? #t])
                 #,body))]))

  (define (init-accumulators tσ body)
    (init-top-σ tσ (init-target-cs (init-target-actions body))))

  (define-syntax-class join-clause
    #:attributes (clause new-σ)
    (pattern [σ*:id (~or (~and #:join (~bind [bindf #'bind-join]))
                         (~and #:join* (~bind [bindf #'bind-join*]))
                         (~and #:alias (~bind [bindf #'bind-alias]))
                         (~and #:alias* (~bind [bindf #'bind-alias*]))) jσ:expr a:expr vs:expr]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bindf (σ* jσ a vs) #,rest)))
    (pattern [res:id (~or (~and #:get (~bind [bindf #'bind-get]))
                          (~and #:get-kont (~bind [bindf #'bind-get-kont]))
                          (~and #:force (~bind [bindf #'bind-force]))
                          (~and #:delay (~bind [bindf #'bind-delay]))) jσ:expr a:expr]
             #:with new-σ #'jσ ;; XXX: not new
             #:attr clause (λ (rest) #`(bindf (res jσ a) #,rest)))
    (pattern [(ρ* σ* δ*) #:bind ρ bσ l δ xs vs]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bind (ρ* σ* δ*) (ρ bσ l δ xs vs) #,rest)))
    (pattern [(ρ* σ* δ*) (~or (~and #:bind-rest (~bind [bindf #'bind-rest]))
                              (~and #:bind-rest-apply (~bind [bindf #'bind-rest-apply])))
              ρ brσ l δ xs r vs]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bindf (ρ* σ* δ*) (ρ brσ l δ xs r vs) #,rest)))
    (pattern [(σ*:id a*:id) #:push bpσ l δ k]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bind-push (σ* a* bpσ l δ k) #,rest)))
    ;; a couple shorthands
    (pattern [σ*:id (~or (~and #:join-forcing (~bind [bindf #'bind-join]))
                         (~and #:join-local-forcing (~bind [bindf #'bind-join-local])))
                    jσ:expr a:expr v:expr]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(do (jσ) ([fs #:force jσ v])
                           (bindf (σ* jσ a fs) #,rest))))
    (pattern [res:id (~or (~and #:in-get (~bind [bindf #'bind-get]))
                          (~and #:in-kont (~bind [bindf #'bind-get-kont]))
                          (~and #:in-force (~bind [bindf #'bind-force]))
                          (~and #:in-delay (~bind [bindf #'bind-delay]))) jσ:expr a:expr]
             #:with new-σ #'jσ ;; XXX: not new
             #:attr clause (λ (rest) #`(bindf (res-tmp jσ a)
                                         (do (jσ) ([res (in-set res-tmp)])
                                           #,rest)))))

  (define-splicing-syntax-class comp-clauses
    #:attributes ((guards 1))
    (pattern (~and (~seq (~or [_:id _:expr]
                              [(_:id ...) _:expr]
                              (~seq #:when _:expr)
                              (~seq #:unless _:expr)) ...+)
                   (~seq guards ...))))

  (define-splicing-syntax-class (join-clauses maybe-prev-σ)
    #:attributes (clauses last-σ)
    (pattern (~seq join:join-clause
                   (~var joins (join-clauses (attribute join.new-σ))))
             #:attr clauses (cons (attribute join.clause)
                                  (attribute joins.clauses))
             #:attr last-σ (attribute joins.last-σ))
    (pattern (~seq) #:attr clauses '()
             #:attr last-σ maybe-prev-σ
             #:fail-unless maybe-prev-σ "Expected at least one join clause"))

  (syntax-parse stx
    [(_ (cσ:id) (c:comp-clauses clauses ...) body:expr ...+)
     ;; build a new fold or a fold that continues adding to the
     ;; outer do's targets. σ is bound to itelf since the body may
     ;; still refer to it. cs go to a new identifier.
     (with-syntax* ([(ttarget-σ ...) (listy (and tσ (generate-temporary #'do-σ)))]
                    [(vtarget-σ ...) (listy (and tσ #'target-σ))]
                    [(textras ...) (append (listy (and tcs (generate-temporary #'cs)))
                                           (listy (and tas (generate-temporary #'actions))))]
                    [(vextras ...) (append (listy (and tcs #'target-cs))
                                           (listy (and tas #'target-actions)))]
                    [(g gs ...) #'(c.guards ...)]
                    #;
                    [(voidc ...) (listy (and add-void? #'[dummy (void)]))])
       (init-accumulators
        #'cσ
        (gen-wrap
         #`(for/fold ([ttarget-σ vtarget-σ] ... [textras vextras] ... #;voidc #;...) (g)
             (syntax-parameterize ([vtarget-σ (make-rename-transformer #'ttarget-σ)] ...
                                   [vextras (make-rename-transformer #'textras)] ...)
               (let ([cσ ttarget-σ] ...)
                 (for*/fold ([ttarget-σ ttarget-σ] ... [textras textras] ... #;voidc #;...) (gs ...)
                   (let ([cσ ttarget-σ] ...)
                     (with-do
                      (do-body-transformer
                       (do (cσ) (clauses ...) body ...)))))))))))]

    ;; if we don't get a store via clauses, σ is the default.
    [(_ (jσ:id) ((~var joins (join-clauses #f)) clauses ...) body:expr ...+)
     (define join-body
       #`(with-do (do (#,(attribute joins.last-σ)) (clauses ...)
                    (do-body-transformer (begin body ...)))))
     (define binds
       (for/fold ([full join-body])
           ([fn (in-list (reverse (attribute joins.clauses)))])
         (fn full)))
     (init-accumulators #'jσ (gen-wrap binds))]

    [(_ (dbσ:id) () body:expr ...+)
     #`(with-do
        #,(init-accumulators
           #'dbσ
           (gen-wrap
            #`(do-body-transformer
               (begin body ... #,@(listy (and add-void? #'(values)))
                      )))))]

    ;; when fold/fold doesn't cut it, we need a safe way to recur.
    [(_ (ℓσ:id) loop:id ([args:id arg0:expr] ...)
        (~optional (~seq #:values num-results:nat))
        body:expr ...+)
     (define extras (append (listy (and tcs #'target-cs))
                            (listy (and tas #'target-actions))))
     (with-syntax ([(argps ...) (generate-temporaries #'(args ...))]
                   [(ttarget-σ ...) (listy (and tσ (generate-temporary #'some-σ)))]
                   [(vtarget-σ ...) (listy (and tσ #'target-σ))]
                   [(targets ...) (append (listy (and tcs (generate-temporary #'some-cs)))
                                          (listy (and tas (generate-temporary #'some-actions))))]
                   [(tvalues ...) (append (listy (and tcs #'target-cs))
                                          (listy (and tas #'target-actions)))])
       ;; no gen-wrap or with-do since this is used in primitives, always nested dos.
       (init-accumulators
        #'ℓσ
        #`(let real-loop ([ttarget-σ vtarget-σ] ... [targets tvalues] ... [args arg0] ...)
            (let ([ℓσ ttarget-σ] ...)
              (syntax-parameterize ([vtarget-σ (make-rename-transformer #'ttarget-σ)] ...
                                    [tvalues (make-rename-transformer #'targets)] ...
                                    #,@(if (attribute num-results)
                                           #`([do-extra-values #,(syntax->datum #'num-results)])
                                           '()))
                ;; make calling the loop seemless.
                ;; Pass the accumulators if they exist.
                (let-syntax ([loop (syntax-rules ()
                                     [(_ σ* argps ...)
                                      (real-loop #,@(listy (and tσ #'σ*))
                                                 #,@extras argps ...)])])
                  body ...))))))]))
