#lang racket
(require (for-syntax syntax/parse racket/match racket/syntax racket/trace)
         racket/stxparam "notation.rkt"
         racket/generator)
(provide continue (for-syntax mk-do listy))

;; Helper for building targets
(define-for-syntax (listy x) (if x (list x) '()))

;; Some primitives don't yield anything. We need a way to do nothing.
(define-syntax (continue stx)
  (syntax-parse stx
    [(_)
     (define tσtcs
       (append (listy (and (syntax-parameter-value #'target-σ?) #'target-σ))
               (listy (and (syntax-parameter-value #'target-cs?) #'target-cs))))
     #`(values #,@tσtcs)]))

(define-syntax-rule (mk-syntax-parameters id ...)
  (begin (define-syntax-parameter id #f) ... (provide id ...)))

(mk-syntax-parameters bind-join bind-join* bind-rest bind do make-var-contour
                      target-σ? target-cs? target-σ target-cs top-σ top-σ?)
;; default: do nothing to the body of a do.
(define-syntax-parameter do-body-transformer (syntax-rules () [(_ e) e]))
(provide do-body-transformer)

(define-syntax-rule (bind-push (σ* a* bpσ l δ k) body)
  (let ([a* (make-var-contour l δ)])
    (bind-join (σ* bpσ a* (set k)) body)))

;; Private
(define-syntax-parameter in-do-ctx? #f)
(define-syntax-rule (with-do body ...)
  (syntax-parameterize ([in-do-ctx? #t]) body ...))

(define-for-syntax ((mk-do σ-∆s? set-monad? global-σ? generators?) stx)
  ;; Construct the values tuple given the previously bound σ and cs
  (define in-do? (syntax-parameter-value #'in-do-ctx?))
  (define tσ (syntax-parameter-value #'target-σ?))
  (define tcs (syntax-parameter-value #'target-cs?))
  (define gen-wrap
    (cond [(or in-do? (not generators?))
           values]
          [(and generators? global-σ? (not σ-∆s?))
           (λ (stx) #`(begin #,stx 'done))]
          [else (λ (stx) #`(begin (yield #,stx) 'done))]))
  (define add-void? (and global-σ? (not σ-∆s?)))
  (define tσtcs
    (append (listy (and tσ #'target-σ))
            (listy (and tcs #'target-cs))))

  (define (init-target-cs body)
    (cond [(and (not in-do?) set-monad?)
           #`(let ([cs ∅])
               (syntax-parameterize ([target-cs (make-rename-transformer #'cs)])
                 #,body))]
          [else body]))

  (define top? (syntax-parameter-value #'top-σ?))
  ;; If the top level store is not already installed by λ%, and we are
  ;; not in the middle of constructing a do form, create a hidden binding
  ;; to track the top level store. While we're at it, create the target store
  ;; binding (in σ-∆s it starts off at '())
  (define (init-top-σ tσ body)
    (cond [(or top? in-do? global-σ?) body]
          [else
           (define σ-id (generate-temporary #'hidden-top))
           #`(let ([#,σ-id #,tσ]
                   #,(if σ-∆s? #`[#,tσ '()] #`[#,tσ #,tσ]))
               (syntax-parameterize ([top-σ (make-rename-transformer #'#,σ-id)]
                                     [target-σ (make-rename-transformer #'#,tσ)]
                                     [top-σ? #t])
                 #,body))]))

  (define-syntax-class join-clause
    #:attributes (clause new-σ)
    (pattern [σ*:id (~or (~and #:join (~bind [bindf #'bind-join]))
                         (~and #:join* (~bind [bindf #'bind-join*])))
                    jσ:expr a:expr vs:expr]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bindf (σ* jσ a vs) #,rest)))
    (pattern [(ρ* σ* δ*) #:bind ρ bσ l δ xs vs]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bind (ρ* σ* δ*) (ρ bσ l δ xs vs) #,rest)))
    (pattern [(ρ* σ* δ*) #:bind-rest ρ brσ l δ xs r vs]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bind-rest (ρ* σ* δ*) (ρ brσ l δ xs r vs) #,rest)))
    (pattern [(σ*:id a*:id) #:push bpσ l δ k]
             #:with new-σ #'σ*
             #:attr clause
             (λ (rest) #`(bind-push (σ* a* bpσ l δ k) #,rest))))

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
                    [(ttarget-cs ...) (listy (and tcs (generate-temporary #'cs)))]
                    [(vtarget-σ ...) (listy (and tσ #'target-σ))]
                    [(vtarget-cs ...) (listy (and tcs #'target-cs))]
                    [(g gs ...) #'(c.guards ...)]
                    [(voidc ...) (listy (and add-void? #'[dummy (void)]))])
       (init-top-σ
        #'cσ
        (init-target-cs
         (gen-wrap
          #`(for/fold ([ttarget-σ vtarget-σ] ... [ttarget-cs vtarget-cs] ... voidc ...) (g)
              (syntax-parameterize ([vtarget-σ (make-rename-transformer #'ttarget-σ)] ...
                                    [vtarget-cs (make-rename-transformer #'ttarget-cs)] ...)
                (let ([cσ ttarget-σ] ...)
                  (for*/fold ([ttarget-σ ttarget-σ] ... [ttarget-cs ttarget-cs] ... voidc ...) (gs ...)
                    (let ([cσ ttarget-σ] ...)
                      (with-do
                       (do-body-transformer
                        (do (cσ) (clauses ...) body ...))))))))))))]

    ;; if we don't get a store via clauses, σ is the default.
    [(_ (jσ:id) ((~var joins (join-clauses #f)) clauses ...) body:expr ...+)
     (define join-body
       #`(with-do (do (#,(attribute joins.last-σ)) (clauses ...)
                    (do-body-transformer (begin body ...)))))
     (define binds
       (for/fold ([full join-body])
           ([fn (in-list (reverse (attribute joins.clauses)))])
         (fn full)))
     (init-top-σ #'jσ (init-target-cs (gen-wrap binds)))]

    [(_ (dbσ:id) () body:expr ...+)
     #`(with-do
        #,(init-top-σ
           #'dbσ
           (init-target-cs
            (gen-wrap
             #`(do-body-transformer
                (begin body ... #,@(listy (and add-void? #'(void)))))))))]

    ;; when fold/fold doesn't cut it, we need a safe way to recur.
    [(_ (ℓσ:id) loop:id ([args:id arg0:expr] ...) body:expr ...+)
     (define tcss (listy (and tcs #'target-cs)))
     (with-syntax ([(argps ...) (generate-temporaries #'(args ...))]
                   [(targets ...) (append (listy (and tσ (generate-temporary #'some-σ)))
                                          (listy (and tcs (generate-temporary #'some-cs))))]
                   [(tvalues ...) tσtcs])
       ;; no gen-wrap or with-do since this is used in primitives, always nested dos.
       (init-top-σ
        #'ℓσ
        (init-target-cs
         #`(let real-loop ([targets tvalues] ... [args arg0] ...)
             (syntax-parameterize ([tvalues (make-rename-transformer #'targets)] ...)
               ;; make calling the loop seemless.
               ;; Pass the accumulators if they exist.
               (let-syntax ([loop (syntax-rules ()
                                    [(_ σ* argps ...)
                                     (real-loop #,@(listy (and tσ #'σ*))
                                                #,@tcss argps ...)])])
                 body ...))))))]))
