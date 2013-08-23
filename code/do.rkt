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

(mk-syntax-parameters 
 ;; change ∨ access σ
 bind-join bind-join*
 bind-alias* bind-big-alias bind-push
 bind bind-rest
 ;; change μ
 bind-μbump bind-μbump*
 ;; change Ξ, access M
 bind-calling-context
 ;; access Ξ
 bind-get-ctx
 ;; change M
 bind-memoize
 ;; access σ
 bind-get bind-get-kont bind-force bind-delay 
 ;; Implicits / should use implicits?
 target-σ? target-μ target-τ target-σ-token
 target-cs? target-cs target-actions? target-actions
 top-σ
 ;; alloc
 make-var-contour
 ;; self
 do)
(define-syntax-parameter target-σ
  (λ (stx) (raise-syntax-error #f (format "To be used within proper scope ~a:~a"
                                          (syntax-source-file-name stx)
                                          (syntax-line stx))
                               stx)))
(define-syntax-parameter abs-count? #f)
(define-syntax-parameter σ-∆s? #f)
(define-syntax-parameter imperative? #f)
(define-syntax-parameter global-σ? #f)
(define-syntax-parameter pushdown? #f)
(define-syntax-parameter compiled? #f)
(define-syntax-parameter fixpoint #f)
(provide target-σ abs-count? compiled? fixpoint σ-∆s? global-σ? imperative? pushdown?)


(define-syntax-rule (bind-τ-join (a τs) . body)
  (let ([τ* (join target-τ a τs)])
    (syntax-parameterize ([target-τ (make-rename-transformer #'τ*)])
      (bind-μbump (a) . body))))

(define-syntax-rule (match-state e [(head σ μ τ . pat) rhss ...] ... [last-pat last-e])
  (match e
    [(head σ μ τ . pat)
     (let ([σ* '()])
      (syntax-parameterize ([top-σ (make-rename-transformer #'σ)]
                            [target-σ (if (syntax-parameter-value #'σ-∆s?)
                                          (make-rename-transformer #'σ*)
                                          (make-rename-transformer #'σ))]
                            [target-μ (make-rename-transformer #'μ)]
                            [target-τ (make-rename-transformer #'τ)])
        rhss ...))] ...
    [last-pat last-e]))

;; default: do nothing to the body of a do.
(define-syntax-parameter do-body-transformer (syntax-rules () [(_ e) e]))
(provide do-body-transformer)

(define-syntax-rule (bind-alias (alias to-alias) body)
  (bind-get (res to-alias) (bind-join (alias res) body)))

(define-for-syntax ((mk-do set-monad? generators?) stx)
  ;; Construct the values tuple given the previously bound σ and cs
  (define σ-∆sv? (syntax-parameter-value #'σ-∆s?))
  (define μ? (syntax-parameter-value #'abs-count?))
  (define tσ (syntax-parameter-value #'target-σ?))
  (define tcs (syntax-parameter-value #'target-cs?))
  (define tas (syntax-parameter-value #'target-actions?))
  (define global-σ?* (syntax-parameter-value #'global-σ?))
  (define gen-wrap
    (cond [(not generators?) values]
          [(and global-σ?* (not σ-∆sv?)) (λ (stx) #`(begin #,stx 'done))]
          [else (λ (stx) #`(begin (yield #,stx) 'done))]))
  (define add-void? (syntax-parameter-value #'imperative?))

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
    (pattern [k*:id #:calling-context ctx:expr k:expr]
             #:attr clause (λ (rest) #`(bind-calling-context (k* ctx k) #,rest)))
    ;; a couple shorthands
    (pattern [(~or (~and #:join-forcing (~bind [bindf #'bind-join]))
                   (~and #:memoize-forcing (~bind [bindf #'bind-memoize]))) a:expr v:expr]
             #:attr clause
             (λ (rest) #`(do ([fs #:force v]) (bindf (a fs) #,rest))))
    (pattern [res:id #:in-kont k]
             #:attr clause (λ (rest) #`(bind-get-kont (res-tmp comprehension k)
                                         (do ([res (comprehension res-tmp)])
                                           #,rest))))
    (pattern [res:id (~or (~and #:in-get (~bind [bindf #'bind-get]))
                          (~and #:in-context (~bind [bindf #'bind-get-ctx]))
                          (~and #:in-force (~bind [bindf #'bind-force]))
                          (~and #:in-delay (~bind [bindf #'bind-delay]))) a:expr]
             #:attr clause (λ (rest) #`(bindf (res-tmp a)
                                         (do ([res (in-set res-tmp)]) #,rest)))))

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
