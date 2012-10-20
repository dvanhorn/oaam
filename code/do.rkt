#lang racket
(require (for-syntax syntax/parse racket/match racket/syntax)
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
     (quasisyntax/loc stx (values #,@tσtcs))]))

(define-syntax-rule (mk-syntax-parameters id ...)
  (begin (define-syntax-parameter id #f) ... (provide id ...)))

(mk-syntax-parameters bind-join bind-join* bind do make-var-contour
                      target-σ? target-cs? target-σ target-cs top-σ top-σ?)

(define-syntax-rule (bind-push (σ* a* σ l δ k) body)
  (let ([a* (make-var-contour l δ)])
    (bind-join (σ* σ a* (set k)) body)))

;; Private
(define-syntax-parameter in-do-ctx? #f)
(define-syntax-rule (with-do body ...)
  (syntax-parameterize ([in-do-ctx? #t]) body ...))

(define-for-syntax (mk-do σ-∆s? set-monad? global-σ? generators?)

  (define (dot in-do-rec? stx)
    ;; Construct the values tuple given the previously bound σ and cs
    (define in-do? (or in-do-rec? (syntax-parameter-value #'in-do-ctx?)))
    (define gen-wrap
      (cond [(or in-do? (not generators?)
                 (not (or (not global-σ?) σ-∆s?)))
             values]
            [else (λ (stx) #`(begin (yield #,stx) 'done))]))
    (define tσ (syntax-parameter-value #'target-σ?))
    (define tcs (syntax-parameter-value #'target-cs?))
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

    ;; If the top level store is not already installed by λ%, and we are
    ;; not in the middle of constructing a do form, create a hidden binding
    ;; to track the top level store. While we're at it, create the target store
    ;; binding (in σ-∆s it starts off at '())
    (define (init-top-σ σ body)
      (let ([top? (syntax-parameter-value #'top-σ?)])
        (cond [(or top? in-do? global-σ?) body]
              [else (define σ-id (generate-temporary))
                    #`(let ([#,σ-id #,σ]
                            #,(if σ-∆s? #`[#,σ '()] #`[#,σ #,σ]))
                        (syntax-parameterize ([top-σ
                                               (make-rename-transformer
                                                #'#,σ-id)]
                                              [target-σ (make-rename-transformer #'#,σ)])
                          #,body))])))

    (define-syntax-class join-clause
      #:attributes (clause new-σ)
      (pattern [σ*:id (~or (~and #:join (~bind [bindf #'bind-join]))
                           (~and #:join* (~bind [bindf #'bind-join*])))
                      σ:expr a:expr vs:expr]
               #:with new-σ #'σ*
               #:attr clause
               (λ (rest) #`(bindf (σ* σ a vs) #,rest)))
      (pattern [(ρ* σ* δ*) #:bind ρ σ l δ xs vs]
               #:with new-σ #'σ*
               #:attr clause
               (λ (rest) #`(bind (ρ* σ* δ*) (ρ σ l δ xs vs) #,rest)))
      (pattern [(σ*:id a*:id) #:push σ l δ k]
               #:with new-σ #'σ*
               #:attr clause
               (λ (rest) #`(bind-push (σ* a* σ l δ k) #,rest))))

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
      [(_ (σ:id) (c:comp-clauses clauses ...) body:expr ...+)
       ;; build a new fold or a fold that continues adding to the
       ;; outer do's targets. σ is bound to itelf since the body may
       ;; still refer to it. cs go to a new identifier.
       (with-syntax* ([(targets ...) tσtcs]
                      [(tvalues ...) tσtcs]
                      [(voidc ...) (listy (and add-void? #'[dummy (void)]))])
         (init-top-σ #'σ
          (init-target-cs
           (gen-wrap
           (quasisyntax/loc stx
             (for*/fold ([targets tvalues] ... voidc ...) (c.guards ...)
               (with-do
                #,(dot #t (syntax/loc stx (do (σ) (clauses ...) body ...))))))))))]

      ;; if we don't get a store via clauses, σ is the default.
      [(_ (σ:id) ((~var joins (join-clauses #f)) clauses ...) body:expr ...+)
       (define join-body
         (dot #t
              (quasisyntax/loc stx
                (do (#,(attribute joins.last-σ)) (clauses ...)
                  (with-do body ...)))))
       (define binds
         (let loop ([j (reverse (attribute joins.clauses))]
                    [full join-body])
           (match j
             [(cons fn js) (loop js (fn full))]
             [_ full])))
       (init-top-σ #'σ (init-target-cs (gen-wrap binds)))]

      [(_ (σ:id) () body:expr ...+)
       (quasisyntax/loc stx
         (with-do
           #,(init-top-σ #'σ
              (init-target-cs
               (quasisyntax/loc stx
                 (begin body ... #,@(listy (and add-void? #'(void)))))))))]

      ;; when fold/fold doesn't cut it, we need a safe way to recur.
      [(_ (σ:id) loop:id ([args:id arg0:expr] ...) body:expr ...+)
       (define tcss (listy (and tcs #'target-cs)))
       (with-syntax* ([(argps ...) (generate-temporaries #'(args ...))])
         (init-top-σ
          #'σ
          (init-target-cs
           (quasisyntax/loc stx
             (let real-loop (#,@(append (listy (and tσ #`[target-σ target-σ]))
                                        (listy (and tcs #`[target-cs target-cs])))
                             [args arg0] ...)
               ;; Make calling the loop seemless.
               ;; Pass the accumulators if they exist.
               (let-syntax ([loop (syntax-rules ()
                                      [(_ σ* argps ...)
                                       (real-loop #,@(listy (and tσ #'σ*))
                                                  #,@tcss argps ...)])])
                   body ...))))))]))
  (λ (stx) (dot #f stx)))
