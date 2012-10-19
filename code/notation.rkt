#lang racket

(require (for-syntax syntax/parse racket/syntax
                     (only-in syntax/struct build-struct-names)
                     racket/list
                     racket/stxparam
                     racket/match
                     syntax/id-table
                     syntax/srcloc)
         (rename-in racket/generator
                    [yield real-yield]
                    [generator real-generator])
         racket/stxparam)
(provide for/union for*/union for/set for*/set
         define-simple-macro*
         ∅ ∅? ∪ ∩ ∖ ∪1 ∪/l ∖1 ∖/l ∈
         mk-op-struct
         continue do
         yield
         bind-join
         bind-join*
         bind make-var-contour
         target-σ? target-cs? target-σ target-cs top-σ
         (for-syntax mk-do init-target-cs init-top-σ))

;; define-simple-macro does not have an implicit quasisyntax.
(define-syntax (define-simple-macro* stx)
  (syntax-parse stx
    [(_ (name:id . pattern) directives ... template)
     (syntax/loc stx
       (define-syntax (name syn)
         (syntax-parse syn
           [(name . pattern) directives ... (quasisyntax/loc syn template)])))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for/union

(begin-for-syntax
 (define-splicing-syntax-class (ops initial)
   #:attributes (init res)
   (pattern (~seq (~or (~optional (~seq #:initial init:expr)
                                  #:defaults ([init initial]))
                       (~optional (~seq #:res res:id)
                                  #:defaults ([res #'acc]))) ...)))
 ;; Helper for building targets
 (define (listy x) (if x (list x) '())))

(define-simple-macro* (for/append (~var o (ops #''())) guards body ...+)
  (for/fold ([o.res o.init]) guards (append (let () body ...) o.res)))

;; Set notations
(define-values (∅ ∅? ∪ ∩ ∖ ∪1 ∪/l ∖1 ∖/l ∈)
  (let ([set-add*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-add s x)))]
        [set-remove*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-remove s x)))]
        [in? (λ (x s) (set-member? s x))])
    (values (set) set-empty? set-union set-intersect set-subtract
            set-add set-add*
            set-remove set-remove* in?)))

(define-simple-macro* (for/union (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro* (for*/union (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro* (for/set (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))
(define-simple-macro* (for*/set (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))

;; Some primitives don't yield anything. We need a way to do nothing.
(define-syntax (continue stx)
  (syntax-parse stx
    [(_)
     (quasisyntax/loc stx
       (values #,@(append (listy (and (syntax-parameter-value #'target-σ?) #'target-σ))
                          (listy (and (syntax-parameter-value #'target-cs?) #'target-cs)))))]))

;; Specialize representations
(define-syntax mk-op-struct
  (syntax-parser
    [(_ name:id (fields:id ...) (subfields:id ...)
        (~bind [container (format-id #'name "~a-container" #'name)]
               [name: (format-id #'name "~a:" #'name)])
        (~optional (~seq #:expander
                         (~or (~and #:with-first-cons
                                    (~bind [expander
                                            #`(syntax-rules ()
                                                [(_ σ #,@(cdr (syntax->list #'(fields ...))))
                                                 (cons σ (container subfields ...))])]))
                              expander:expr)) ;; want a different match expander?
                   #:defaults ([expander
                                #'(syntax-rules ()
                                    [(_ fields ...)
                                     (container subfields ...)])])))
     #:do [(define (populate fs)
             (let ([start (make-free-id-table)])
               (for ([f (in-list fs)]) (free-id-table-set! start f #t))
               start))
           (define fieldsl (syntax->list #'(fields ...)))
           (define subfieldsl (syntax->list #'(subfields ...)))
           (define fs (populate fieldsl))
           (define sfs (populate subfieldsl))
           (match-define (list-rest _ _ name? sels)
                         (build-struct-names #'name fieldsl #f #t #'name))
           (match-define (list-rest _ _ real-name? real-sels)
                         (build-struct-names #'container fieldsl #f #t #'container))
           (define-values (good-sels bad-sels)
             (for/fold ([good '()] [bad '()]) ([f (in-list fieldsl)]
                                               [sel (in-list sels)]
                                               [real (in-list real-sels)])
               ;; Supposed field is actually present. Pair the container's
               ;; selector with the desired selector name.
               (cond [(free-id-table-ref sfs f #f)
                      (values `((,sel ,real) . ,good) bad)]
                     [else (values good (cons sel bad))])))]
     #:fail-unless (for/and ([s (in-list subfieldsl)])
                     (free-id-table-ref fs s #f))
     "Subfields should be contained in fields list."
     (with-syntax ([((good real-good) ...) good-sels]
                   [(bad ...) bad-sels])
     #`(begin (struct container (subfields ...) #:prefab)
              (define-syntax (name syn)
                (syntax-parse syn
                  [(_ fields ...) #'(container subfields ...)]
                  [n:id (raise-syntax-error #f "Not first class" syn)]))
              (define #,name? #,real-name?)
              (define good real-good) ...
              ;; Make sure things compile but I get good error messages
              ;; if I have runtime logic errors.
              (define (bad . rest)
                (error 'bad "Not present in specialized representation")) ...
              (define-match-expander name: expander)))]))

(define-syntax-parameter yield
  (λ (stx)
     (raise-syntax-error #f "Must be within the context of a generator" stx)))

(define-for-syntax (mk-analysis-err stx)
  (raise-syntax-error #f "For use in mk-analysis and its input transformers" stx))
(define-syntax-parameter bind-join mk-analysis-err)
(define-syntax-parameter bind-join* mk-analysis-err)

(define-syntax-parameter make-var-contour #f)
(define-syntax-rule (bind-push (σ* a* σ l δ k) body)
  (let ([a* (make-var-contour l δ)])
    (bind-join (σ* σ a* (set k)) body)))

(define-syntax-parameter bind mk-analysis-err)
(define-syntax-parameter do #f) ;; to give to primitives
;; What is do folding over?
(define-syntax-parameter target-σ? #f)
(define-syntax-parameter target-cs? #f)
(define-syntax-parameter target-σ
  (λ (stx) (syntax-case stx () [_ (raise-syntax-error #f "Must be bound" stx)])))
(define-syntax-parameter top-σ #f) ;; For σ-∆s only. Keep a binding to the given store.
(define-syntax-parameter target-cs #f)
;; Private
(define-syntax-parameter in-do-ctx? #f)

(define-for-syntax (init-target-cs in-do? set-monad? body)
  (let ([tcs (or (syntax-parameter-value #'target-cs?)
                 set-monad?)])
    (cond [(and tcs (boolean? tcs))
           #`(let ([cs ∅])
                  (syntax-parameterize ([target-cs (make-rename-transformer #'cs)])
                    #,body))]
          [else body])))

(define-for-syntax (init-top-σ in-do? σ-∆s? σ body)
  (cond [(or in-do? (not σ-∆s?)) body]
        [else (define σ-id (generate-temporary #'top-σ))
              #`(let ([#,σ-id #,σ]
                      #,@(if σ-∆s? (list #`[#,σ '()]) (list #`[#,σ #,σ])))
                  (syntax-parameterize ([top-σ (make-rename-transformer #'#,σ-id)]
                                        [target-σ (make-rename-transformer #'#,σ)])
                    #,body))]))

(define-for-syntax (mk-do σ-∆s? set-monad? global-σ? generators?)

  (define (dot in-do-rec? stx)
    ;; Construct the values tuple given the previously bound σ and cs
    (define in-do? (or in-do-rec? (syntax-parameter-value #'in-do-ctx?)))
    (define gen-wrap
      (if (or in-do? (not generators?)
              (not (or (not global-σ?) σ-∆s?)))
          values
          (λ (stx) #`(begin (real-yield #,stx) 'done))))
    (define tσ (syntax-parameter-value #'target-σ?))
    (define tcs (syntax-parameter-value #'target-cs?))
    (define add-void? (and global-σ? (not σ-∆s?)))

    (define-syntax-class join-clause
      #:attributes (clause new-σ)
      (pattern [σ*:id (~or (~and #:join (~bind [bindf #'bind-join]))
                           (~and #:join* (~bind [bindf #'bind-join*])))
                      σ:expr a:expr vs:expr]
               #:with new-σ #'σ*
               #:attr clause
               (λ (rest) #`(bindf (σ* σ a vs) #,rest)))
      (pattern [(ρ* σ* δ*) #:bind ρ σ l δ xs vs] ;; these vals don't get hoisted
               #:with new-σ #'σ*
               #:attr clause
               (λ (rest) #`(bind (ρ* σ* δ*) (ρ σ l δ xs vs) #,rest)))
      (pattern [(σ*:id a*:id) #:push σ l δ k] ;; no vals to hoist.
               #:with new-σ #'σ*
               #:attr clause
               (λ (rest) #`(bind-push (σ* a* σ l δ k) #,rest))))

    (define-splicing-syntax-class comp-clauses
      #:attributes ((guards 1))
      (pattern (~and (~seq (~or [x:id e:expr]
                                [(xs:id ...) ev:expr]
                                (~seq #:when guardw:expr)
                                (~seq #:unless guardu:expr)) ...+)
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
       (with-syntax* ([(do-targets ...)
                       (append (listy (and tσ #'target-σ))
                               (listy (and tcs #'target-cs)))]
                      [(targets ...)
                       (append (listy (and tσ #'σ))
                               (listy (and tcs (generate-temporary))))]
                      [(tvalues ...)
                       (append (listy (and tσ #'σ))
                               (listy (and tcs
                                           (if in-do? #'target-cs #'∅))))]
                      [(g gs ...) #'(c.guards ...)]
                      [(voidc ...) (if add-void? #'([dummy (void)]) #'())])
         (init-top-σ in-do? σ-∆s?
          #'σ
          (gen-wrap
           (quasisyntax/loc stx
             (for/fold ([targets tvalues] ... voidc ...) (g)
               (syntax-parameterize ([do-targets (make-rename-transformer #'targets)] ...)
                 (for*/fold ([targets tvalues] ... voidc ...) (gs ...)
                   (syntax-parameterize ([in-do-ctx? #t])
                     #,(dot #t (syntax/loc stx (do (σ) (clauses ...) body ...)))))))))))]
      ;; if we don't get a store via clauses, σ is the default.
      [(_ (σ:id) ((~var joins (join-clauses #f)) clauses ...) body:expr ...+)
       (define inner-σ (or (attribute joins.last-σ) #'σ))
       (define binds
         (let loop ([j (reverse (attribute joins.clauses))]
                    [full (dot #t
                               (quasisyntax/loc stx
                                 (do (#,inner-σ) (clauses ...)
                                   (syntax-parameterize ([in-do-ctx? #t])
                                     body ...))))])
           (match j
             [(cons fn js) (loop js (fn full))]
             [_ full])))        
       (init-top-σ in-do? σ-∆s? #'σ (gen-wrap binds))]
      [(_ (σ:id) (blob clauses ...) body:expr ...+)
       (raise-syntax-error #f "Expected for-clause or join clause." #'blob)]
      [(_ (σ:id) () body:expr ...+)
       (quasisyntax/loc stx
         (syntax-parameterize ([in-do-ctx? #t])
           #,(init-top-σ in-do? σ-∆s? #'σ
              (init-target-cs
               in-do? set-monad?
               (quasisyntax/loc stx (begin body ... #,@(listy (and add-void? #'(void)))))))))]
      ;; When fold/fold doesn't cut it, we need a safe way to recur.
      [(_ (σ:id) loop:id ([args:id arg0:expr] ...) body:expr ...+)
       (define tσs (listy (and tσ #'target-σ)))
       (define tcss (listy (and tcs #'target-cs)))
       (with-syntax* ([tcs* (generate-temporary 'tcs*)]
                      [(do-targets ...) (append tσs tcss)]
                      [(new-targets ...) (append (listy (and tσ #'σ))
                                                 (listy (and tcs #'tcs*)))]
                      [(argps ...) (generate-temporaries #'(args ...))])
         (init-top-σ in-do? σ-∆s?
          #'σ
          (init-target-cs
           in-do?
           set-monad?
           (quasisyntax/loc stx
             (let real-loop (#,@(append (listy (and tσ #`[σ target-σ]))
                                        (listy (and tcs #`[tcs* target-cs])))
                             [args arg0] ...)
               (syntax-parameterize ([do-targets (make-rename-transformer #'new-targets)] ...)
                 ;; Make calling the loop seemless.
                 ;; Pass the accumulators if they exist.
                 (let-syntax ([loop (syntax-rules ()
                                      [(_ σ* argps ...)
                                       (real-loop #,@(listy (and tσ #'σ*))
                                                  #,@tcss argps ...)])])
                   body ...)))))))]
      [(_ blob . rest) (raise-syntax-error #f "Expected default store." #'blob)]
      [(_ . rest) (raise-syntax-error #f "Complete fail" stx)]
      [_ (raise-syntax-error #f "Must be applied" stx)]))
  (λ (stx) (dot #f stx)))