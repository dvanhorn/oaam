#lang racket

(require (for-syntax syntax/parse racket/syntax
                     racket/list
                     racket/stxparam
                     racket/match)
         racket/stxparam)
(provide for/union for*/union for/set for*/set
         define-simple-macro*
         ∅ ∪ ∩ ∖ ∪1 ∪/l ∖1 ∖/l ∈
         mk-op-struct
         continue do
         yield
         bind-join
         bind-join*
         bind-push
         bind
         target-σ? target-cs? target-σ target-cs
         (for-syntax mk-do init-target-cs))

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
(define-values (∅ ∪ ∩ ∖ ∪1 ∪/l ∖1 ∖/l ∈)
  (let ([set-add*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-add s x)))]
        [set-remove*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-remove s x)))]
        [in? (λ (x s) (set-member? s x))])
    (values (set) set-union set-intersect set-subtract
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
     #:fail-unless (for/and ([s (in-list (syntax->list #'(subfields ...)))])
                     (for/or ([f (in-list (syntax->list #'(fields ...)))])
                       (free-identifier=? f s)))
     "Subfields should be contained in fields list."
     #'(begin (struct container (subfields ...) #:prefab)
              (define-syntax-rule (name fields ...) (container subfields ...))
              (define-match-expander name: expander))]))

(define-syntax-parameter yield
  (λ (stx)
     (raise-syntax-error #f "Must be within the context of a generator" stx)))

(define-for-syntax (mk-analysis-err stx)
  (raise-syntax-error #f "For use in mk-analysis and its input transformers" stx))
(define-syntax-parameter bind-join mk-analysis-err)
(define-syntax-parameter bind-join* mk-analysis-err)
(define-syntax-parameter bind-push mk-analysis-err)
(define-syntax-parameter bind mk-analysis-err)
(define-syntax-parameter do #f) ;; to give to primitives
;; What is do folding over?
(define-syntax-parameter target-σ? #f)
(define-syntax-parameter target-cs? #f)
(define-syntax-parameter target-σ
  (λ (stx) (syntax-case stx () [_ (raise-syntax-error #f "Must be bound" stx)])))
(define-syntax-parameter target-cs #f)
;; Private
(define-syntax-parameter in-do-ctx? #f)

(define-for-syntax (init-target-cs set-monad?)
  (let ([tcs (or (syntax-parameter-value #'target-cs?) set-monad?)])
    (cond [(and tcs (boolean? tcs))
           (λ (body)
              #`(let ([cs ∅])
                  (syntax-parameterize ([target-cs (make-rename-transformer #'cs)])
                    #,body)))]
          [else values])))

(define-for-syntax (mk-do σ-∆s? set-monad? global-σ? generators?)
  (define (dot stx)
    ;; Construct the values tuple given the previously bound σ and cs
    (define in-do? (syntax-parameter-value #'in-do-ctx?))
    (define gen-wrap
      (if (or in-do? (not generators?)
              (not (or (not global-σ?) σ-∆s?)))
          values
          (λ (stx) `(begin (real-yield #,stx) 'done))))
    (define (bind-rest inner-σ body)
      #`(syntax-parameterize ([target-σ (make-rename-transformer #'#,inner-σ)])
          #,body))
    (define-syntax-class (join-clause replace-v outer-σ body)
      #:attributes (clause new-σ val)
      (pattern [σ*:id (~or (~and #:join (~bind [bindf #'bind-join]))
                           (~and #:join* (~bind [bindf #'bind-join*]))) σ:expr a:expr vs:expr]
               #:with new-σ #'σ* #:attr val #'vs
               #:attr clause
               (λ (rest)
                  #`(bindf (σ* σ a #,(or replace-v #'vs)) #,(bind-rest #'σ* rest))))
      (pattern [(ρ* σ* δ*) #:bind ρ σ l δ xs vs] ;; these vals don't get hoisted
               #:with new-σ #'σ* #:attr val #f
               #:attr clause
               (λ (rest)
                  #`(bind (ρ* σ* δ*) (ρ σ l δ xs vs) #,(bind-rest #'σ* rest))))
      (pattern [(σ*:id a*:id) #:push σ l δ k] ;; no vals to hoist.
               #:with new-σ #'σ* #:attr val #f
               #:attr clause
               (λ (rest)
                  #`(bind-push (σ* a* σ l δ k) #,(bind-rest #'σ* rest)))))

    (define-splicing-syntax-class comp-clauses
      #:attributes ((guards 1))
      (pattern (~and (~seq (~or [x:id e:expr]
                                [(xs:id ...) ev:expr]
                                (~seq #:when guardw:expr)
                                (~seq #:unless guardu:expr)) ...+)
                     (~seq guards ...))))

    ;; A terrible binding pattern is necessary for store deltas. We /hoist/
    ;; the values that are used in join so they are in scope of the real σ.
    (define-splicing-syntax-class (join-clauses maybe-prev-σ outer-σ body)
      #:attributes (clauses (ids 1) (vs 1) (prev-σs 1) last-σ)
      (pattern (~seq (~bind [new-id (generate-temporary)])
                     (~var join (join-clause (and σ-∆s? #'new-id)
                                             outer-σ body))
                     (~var joins (join-clauses (attribute join.new-σ) outer-σ body)))
               #:attr clauses (cons (attribute join.clause)
                                    (attribute joins.clauses))
               #:do [(define v (attribute join.val))
                     (define ids* (attribute joins.ids))
                     (define vs* (attribute joins.vs))]
               #:attr (ids 1) (if v (cons #'new-id ids*) ids*)
               #:attr (vs 1) (if v (cons v vs*) vs*)
               #:attr (prev-σs 1) (if v
                                      (if maybe-prev-σ
                                          (cons maybe-prev-σ (attribute joins.prev-σs))
                                          (cons outer-σ (attribute joins.prev-σs)))
                                      (attribute joins.prev-σs))
               #:attr last-σ (attribute joins.last-σ))
      (pattern (~seq) #:attr clauses '() #:attr (ids 1) '() #:attr (vs 1) '()
               #:attr (prev-σs 1) '()
               #:attr last-σ maybe-prev-σ
               #:fail-unless maybe-prev-σ "Expected at least one join clause"))
    (syntax-parse stx
      [(_ (σ:id) (c:comp-clauses clauses ...) body:expr)
       ;; build a new fold or a fold that continues adding to the
       ;; outer do's targets.
       ;; Make sure the targets are determine at the right time during
       ;; expansion
       (gen-wrap
        #`(let-syntax
              ([folder
                (...
                 (λ (stx)
                    (syntax-parse stx
                      [(_ prev-σ (gs ...) body*)
                       (define tσ (syntax-parameter-value #'target-σ?))
                       (define tcs (syntax-parameter-value #'target-cs?))
                       (with-syntax* ([(do-targets ...)
                                       (append (if tσ (list #'target-σ) '())
                                               (if tcs (list #'target-cs) '()))]
                                      [(targets ...) (generate-temporaries #'(do-targets ...))]
                                      [(tvalues ...)
                                       (append (listy (and tσ #'prev-σ))
                                               (if tcs
                                                   (if #,in-do?
                                                       (list #'target-cs)
                                                       (list #'∅))
                                                   '()))])
                         (syntax/loc stx
                           (for*/fold ([targets tvalues] ...) (gs ...)
                             (syntax-parameterize ([do-targets (make-rename-transformer #'targets)] ...)
                               body*))))])))])
            (folder σ (c.guards ...)
                    (syntax-parameterize ([in-do-ctx? #t])
                      #,(dot #'(#f (σ) (clauses ...) body))))))]
      ;; if we don't get a store via clauses, σ is the default.
      [(_ (σ:id) (joins clauses ...) body:expr)
       ;; This necessitates an order that do-targets is specified.
       ;; First store, then states
       #:declare joins (join-clauses #f #'σ #'body)
       ;; flags conflate imperative store and imperative worklist in wide case
       ;; store-passing/store-δ-accumulation is needed if
       ;; ¬wide or (¬pre-alloc and ¬imperative)
       ;; ≡ ¬(wide and (pre-alloc or imperative))
       (define inner-σ (or (attribute joins.last-σ) #'σ))
       (define binds (let loop ([j (reverse (attribute joins.clauses))]
                                [full (dot #`(#f (#,inner-σ)
                                                (clauses ...)
                                              (syntax-parameterize ([in-do-ctx? #t])
                                                body)))])
                       (match j
                         [(cons fn js) (loop js (fn full))]
                         [_ full])))
       (define hoist-binds
         (if σ-∆s?
             (if global-σ?
                 #'([joins.ids joins.vs] ...)
                 #'([joins.ids (let ([joins.prev-σs σ]) joins.vs)] ...))
             #'())) 
       (quasisyntax/loc stx (let #,hoist-binds #,(gen-wrap binds)))]
      [(_ (σ:id) (blob clauses ...) body:expr)
       (raise-syntax-error #f "Expected for-clause or join clause." #'blob)]
      [(_ (σ:id) (blob clauses ...) body ...)
       (raise-syntax-error #f "Expected single expression body" #'(body ...))]
      [(_ (σ:id) () body:expr)
       #`(syntax-parameterize ([in-do-ctx? #t])
           body)]
      ;; When fold/fold doesn't cut it, we need a safe way to recur.
      [(_ (σ:id) loop:id ([args:id arg0:expr] ...) body:expr)
       (define tσ (syntax-parameter-value #'target-σ?))
       (define tcs (syntax-parameter-value #'target-cs?))
       (define tσs (if tσ (list #'target-σ) '()))
       (define tcss (if tcs (list #'target-cs) '()))
       (with-syntax ([(do-targets ...) (append tσs tcss)]
                     [(new-targets ...) (append (if tσ (list #'tσ) '())
                                                (if tcs (list #'tcs) '()))]
                     [(argps ...) (generate-temporaries #'(args ...))])
         ((init-target-cs set-monad?)
          (quasisyntax/loc stx
            (let real-loop (#,@(append (if tσ (list #`[tσ target-σ]) '())
                                       (if tcs (list #`[tcs target-cs]) '()))
                            [args arg0] ...)
              (syntax-parameterize ([do-targets (make-rename-transformer #'new-targets)] ...)
                (let-syntax ([loop (syntax-rules ()
                                     [(_ σ* argps ...)
                                      (real-loop #,@(if tσ (list #'σ*) '())
                                                 #,@tcss argps ...)])])
                  body))))))]
      [(_ blob . rest) (raise-syntax-error #f "Expected default store." #'blob)]
      [(_ . rest) (raise-syntax-error #f "Complete fail" stx)]
      [_ (raise-syntax-error #f "Must be applied" stx)]))
  dot)