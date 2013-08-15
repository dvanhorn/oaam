#lang racket
(require (for-syntax syntax/parse racket/syntax unstable/syntax)
         racket/stxparam "notation.rkt" "data.rkt" "env.rkt"
         racket/generator)
(provide continue bind-alias match-state (for-syntax mk-do listy))

;; Helper for building targets
(define-for-syntax (listy x) (if x (list x) '()))

;; Some primitives don't yield anything. We need a way to do nothing.
(define-syntax (continue stx)
  (syntax-parse stx
    [(_)
     #`(values 
        #,@(let ([tσ (syntax-parameter-value #'target-σ?)])
             (append (listy (and tσ #'target-σ))
                     (listy (and tσ #'target-μ))
                     (listy (and (syntax-parameter-value #'target-cs?) #'target-cs))
                     (listy (and (syntax-parameter-value #'target-actions?) #'target-actions)))))]))

(define-for-syntax param-id (compose rename-transformer-target syntax-parameter-value))

(define-syntax-rule (mk-syntax-parameters id ...)
  (begin (define-syntax-parameter id #f) ... (provide id ...)))

(mk-syntax-parameters bind-join bind-join* bind-μbump
                      bind-alias* bind-big-alias
                      bind-get bind-force bind-delay
                      bind bind-rest do make-var-contour
                      target-σ? target-μ target-τ
                      target-cs? target-cs target-actions? target-actions
                      top-σ top-σ?)
(define-syntax-parameter target-σ
  (λ (stx) (raise-syntax-error #f (format "To be used within proper scope ~a:~a"
                                          (syntax-source-file-name stx)
                                          (syntax-line stx))
                               stx)))
(provide target-σ)

(define-syntax-rule (bind-τ-join (a τs) . body)
  (let ([τ* (join target-τ a τs)])
    (syntax-parameterize ([target-τ (make-rename-transformer #'τ*)])
      (bind-μbump (a) . body))))

(define-syntax-rule (match-state e [(head σ μ . pat) rhss ...] ... [last-pat last-e])
  (match e
    [(head σ μ . pat)
     (syntax-parameterize ([target-σ (make-rename-transformer #'σ)]
                           [target-μ (make-rename-transformer #'μ)])
       rhss ...)] ...
    [last-pat last-e]))

;; default: do nothing to the body of a do.
(define-syntax-parameter do-body-transformer (syntax-rules () [(_ e) e]))
(provide do-body-transformer)

(define-syntax-rule (bind-push (a* l δ k) body)
  (let ([a* (make-var-contour l δ)])
    (bind-join (a* (singleton k)) body)))

(define-syntax-rule (bind-alias (alias to-alias) body)
  (bind-get (res to-alias) (bind-join (alias res) body)))

(define-for-syntax ((mk-do σ-∆s? set-monad? global-σ? generators? μ?) stx)
  ;; Construct the values tuple given the previously bound σ and cs
  (define tσ (syntax-parameter-value #'target-σ?))
  (define tcs (syntax-parameter-value #'target-cs?))
  (define tas (syntax-parameter-value #'target-actions?))
  (define gen-wrap
    (cond [(not generators?) values]
          [(and global-σ? (not σ-∆s?)) (λ (stx) #`(begin #,stx 'done))]
          [else (λ (stx) #`(begin (yield #,stx) 'done))]))
  (define add-void? (and global-σ? (not σ-∆s?) (not tas)))

  (define-syntax-class join-clause
    #:attributes (clause)
    (pattern [(~or (~and #:join (~bind [bindf #'bind-join]))
                   (~and #:τ-join (~bind [bindf #'bind-τ-join]))
                   (~and #:join* (~bind [bindf #'bind-join*]))
                   (~and #:alias (~bind [bindf #'bind-alias]))
                   (~and #:alias* (~bind [bindf #'bind-alias*]))) a:expr vs:expr]
             #:attr clause
             (λ (rest) #`(bindf (a vs) #,rest)))
    (pattern [res:id (~or (~and #:get (~bind [bindf #'bind-get]))
                          (~and #:force (~bind [bindf #'bind-force]))
                          (~and #:delay (~bind [bindf #'bind-delay]))) a:expr]
             #:attr clause (λ (rest) #`(bindf (res a) #,rest)))
    (pattern [(ρ* δ*) #:bind ρ l δ xs vs]
             #:attr clause
             (λ (rest) #`(bind (ρ* δ*) (ρ l δ xs vs) #,rest)))
    (pattern [(ρ* δ*) #:bind-rest ρ l δ xs r vs]
             #:attr clause
             (λ (rest) #`(bind-rest (ρ* δ*) (ρ l δ xs r vs) #,rest)))
    (pattern [a*:id #:push l δ k]
             #:attr clause
             (λ (rest) #`(bind-push (a* l δ k) #,rest)))
    ;; a couple shorthands
    (pattern [#:join-forcing a:expr v:expr]
             #:attr clause
             (λ (rest) #`(do ([fs #:force v])
                           (bind-join (a fs) #,rest))))
    (pattern [res:id (~or (~and #:in-get (~bind [bindf #'bind-get]))
                          (~and #:in-force (~bind [bindf #'bind-force]))
                          (~and #:in-delay (~bind [bindf #'bind-delay]))) a:expr]
             #:attr clause (λ (rest) #`(bindf (res-tmp a)
                                         (do ([res (in-set res-tmp)])
                                           #,rest)))))

  (define-splicing-syntax-class comp-clauses
    #:attributes ((guards 1))
    (pattern (~and (~seq (~or [_:id _:expr]
                              [(_:id ...) _:expr]
                              (~seq #:when _:expr)
                              (~seq #:unless _:expr)) ...+)
                   (~seq guards ...))))
  (syntax-parse stx
    [(_ () body:expr ...+)
     (gen-wrap
      #`(do-body-transformer
         (let () body ... #,@(listy (and add-void? #'(void))))))]

    [(_ (c:comp-clauses clauses ...) body:expr ...+)
     ;; build a new fold or a fold that continues adding to the
     ;; outer do's targets. σ is bound to itelf since the body may
     ;; still refer to it. cs go to a new identifier.
     (with-syntax* ([(ttarget-σ ...) (listy (and tσ (generate-temporary #'do-σ)))]
                    [(ttarget-μ ...) (listy (and tσ μ? (generate-temporary #'do-μ)))]
                    [(vtarget-σ ...) (listy (and tσ #'target-σ))]
                    [(vtarget-μ ...) (listy (and tσ μ? #'target-μ))]
                    [(textras ...) (append (listy (and tcs (generate-temporary #'cs)))
                                           (listy (and tas (generate-temporary #'actions))))]
                    [(vextras ...) (append (listy (and tcs #'target-cs))
                                           (listy (and tas #'target-actions)))]
                    [(g gs ...) #'(c.guards ...)]
                    [(voidc ...) (listy (and add-void? #'[dummy (void)]))])
       (gen-wrap
        #`(for/fold ([ttarget-σ vtarget-σ] ... [ttarget-μ vtarget-μ] ... [textras vextras] ... voidc ...) (g)
            (syntax-parameterize ([vtarget-σ (make-rename-transformer #'ttarget-σ)] ...
                                  [vtarget-μ (make-rename-transformer #'ttarget-μ)] ...
                                  [vextras (make-rename-transformer #'textras)] ...)
              (for*/fold ([ttarget-σ ttarget-σ] ... [ttarget-μ ttarget-μ] ...
                          [textras textras] ... voidc ...) (gs ...)
                (do-body-transformer
                 (do (clauses ...) body ...)))))))]

    ;; if we don't get a store via clauses, σ is the default.
    [(_ (joins:join-clause ... clauses ...) body:expr ...+)
     (define join-body
       #`(do (clauses ...)
             (do-body-transformer (let () body ...))))
     (define binds
       (for/fold ([full join-body])
           ([fn (in-list (reverse (attribute joins.clause)))])
         (fn full)))
     (gen-wrap binds)]

    ;; when fold/fold doesn't cut it, we need a safe way to recur.
    [(_ loop:id ([args:id arg0:expr] ...) body:expr ...+)
     (define extras (append (listy (and tcs #'target-cs))
                            (listy (and tas #'target-actions))))
     (with-syntax ([(argps ...) (generate-temporaries #'(args ...))]
                   [(ttarget-σ ...) (listy (and tσ (generate-temporary #'some-σ)))]
                   [(vtarget-σ ...) (listy (and tσ #'target-σ))]
                   [(ttarget-μ ...) (listy (and tσ μ? (generate-temporary #'some-μ)))]
                   [(vtarget-μ ...) (listy (and tσ μ? #'target-μ))]
                   [(targets ...) (append (listy (and tcs (generate-temporary #'some-cs)))
                                          (listy (and tas (generate-temporary #'some-actions))))]
                   [(tvalues ...) (append (listy (and tcs #'target-cs))
                                          (listy (and tas #'target-actions)))])
       ;; no gen-wrap since this is used in primitives, always nested dos.
       #`(let real-loop ([ttarget-σ vtarget-σ] ...
                         [ttarget-μ vtarget-μ] ...
                         ;; XXX: Add ttarget-τ if we ever update τ in a loop
                         [targets tvalues] ... [args arg0] ...)
           (syntax-parameterize ([vtarget-σ (make-rename-transformer #'ttarget-σ)] ...
                                 [vtarget-μ (make-rename-transformer #'ttarget-μ)] ...
                                 [tvalues (make-rename-transformer #'targets)] ...)
             ;; make calling the loop seemless.
             ;; Pass the accumulators if they exist.
             (let-syntax ([loop (syntax-rules ()
                                  [(_ argps ...)
                                   (real-loop ttarget-σ ... ttarget-μ ... #,@extras argps ...)])])
               body ...))))]))
