#lang racket

(require (for-syntax syntax/parse racket/syntax
                     racket/stxparam
                     racket/match)
         syntax/parse/define
         racket/stxparam)
(provide for/union for*/union for/set for*/set
         ∅ ∪ ∩ ∖ ∪1 ∪/l ∖1 ∖/l ∈
         mk-op-struct
         bind-join-one
         bind-join
         bind-join*
         bind-push
         bind
         target-σ target-cs
         (for-syntax mk-do))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for/union

(begin-for-syntax
 (define-splicing-syntax-class (ops initial)
   #:attributes (init res)
   (pattern (~seq (~or (~optional (~seq #:initial init:expr)
                                  #:defaults ([init initial]))
                       (~optional (~seq #:res res:id)
                                  #:defaults ([res #'acc]))) ...))))

(define-simple-macro (for/append (~var o (ops #''())) guards body ...+)
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

(define-simple-macro (for/union (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro (for*/union (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro (for/set (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))
(define-simple-macro (for*/set (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))

;; Specialize representations
(define-syntax mk-op-struct
  (syntax-parser
    [(_ stx name:id (fields:id ...) (subfields:id ...)
        (~optional (~seq #:expander expander:expr) ;; want a different match expander?
                   #:defaults ([expander
                                #'(λ (stx)
                                     (syntax-case stx ()
                                       [(_ fields ...)
                                        #'(container subfields ...)]))])))
     #:fail-unless (for/and ([s (in-list (syntax->list #'(subfields ...)))])
                     (for/or ([f (in-list (syntax->list #'(fields ...)))])
                       (free-identifier=? f s)))
     "Subfields should be contained in fields list."
     (with-syntax* ([container (format-id #'name "~a-container" #'name)]
                    [name: (format-id #'name "~a:" #'name)])
       #'(begin (struct container (subfields ...) #:prefab)
                (define-syntax-rule (name fields ...) (container subfields ...))
                (define-match-expander name: expander)))]))

(define-syntax-parameter bind-join-one #f)
(define-syntax-parameter bind-join #f)
(define-syntax-parameter bind-join* #f)
(define-syntax-parameter bind-push #f)
(define-syntax-parameter bind #f)
;; What is do folding over?
(define-syntax-parameter target-σ #f)
(define-syntax-parameter target-cs #f)
(define-syntax-parameter do-body-transformer #f)
;; Private
(define-syntax-parameter in-do-ctx? #f)

(define-for-syntax ((mk-do σ-∆s? set-monad? global-σ? generators?) stx)
  ;; Construct the values tuple given the previously bound σ and cs
  (define in-do? (syntax-parameter-value #'in-do-ctx?))
  (define-syntax-class (join-clause replace-v outer-σ body)
    #:attributes (clause new-σ val)
    (pattern [σ*:id (~or (~and #:set (~bind [bindf #'bind-join-one]))
                         (~and #:join (~bind [bindf #'bind-join]))
                         (~and #:join* (~bind [bindf #'bind-join*]))) σ:expr a:expr v:expr]
             #:with new-σ #'σ* #:attr val #'v
             #:attr clause
             (λ (rest)
                #`(bindf (σ* σ a #,(or replace-v #'v))
                         (syntax-parameterize ([target-σ (and (syntax-parameter-value #'target-σ)
                                                              (make-rename-transformer #'σ*))])
                           #,rest))))
    (pattern [(ρ* σ* δ*) #:bind ρ σ l δ xs vs] ;; these vals don't get hoisted
             #:with new-σ #'σ* #:attr val #f
             #:attr clause
             (λ (rest)
                #`(bind (ρ* σ* δ*) (ρ σ l δ xs vs)
                        (syntax-parameterize ([target-σ (and (syntax-parameter-value #'target-σ)
                                                             (make-rename-transformer #'σ*))])
                          #,rest))))
    (pattern [(σ*:id a*:id) #:push σ l δ k] ;; no vals to hoist.
             #:with new-σ #'σ* #:attr val #f
             #:attr clause
             (λ (rest)
                #`(bind-push (σ* a* σ δ l ρ k)
                             (syntax-parameterize ([target-σ (and (syntax-parameter-value #'target-σ)
                                                                  (make-rename-transformer #'σ*))])
                               #,rest)))))

  (define-splicing-syntax-class (comp-clauses prev-σ outer-σ body)
    #:attributes (clause)
    (pattern (~and (~seq (~or [x:id e:expr]
                              [(xs:id ...) ev:expr]
                              (~seq #:when guardw:expr)
                              (~seq #:unless guardu:expr)) ...)
                   (~seq guards ...))
             #:attr clause
             ;; build a new fold or a fold that continues adding to the
             ;; outer do's targets.
             (let* ([listy (λ (x) (if x (list x) '()))]
                    [gen-wrap
                     (if (or in-do? (not generators?)
                             (not (or (not global-σ?)
                                      σ-∆s?)))
                         values
                         (λ (stx) `(begin (real-yield #,stx) 'done)))])
               (λ (rest)
                  (with-syntax* ([(do-targets ...)
                                  (append (listy (syntax-parameter-value #'target-σ))
                                          (listy (syntax-parameter-value #'target-cs)))]
                                 [(targets ...) (generate-temporaries #'(do-targets ...))]
                                 [(tvalues ...)
                                  (append (listy (and (syntax-parameter-value #'target-σ)
                                                      prev-σ))
                                          (listy (syntax-parameter-value #'target-cs)))])
                    (gen-wrap
                     #`(for*/fold ([targets tvalues] ...)
                           (guards ...)
                         (syntax-parameterize ([do-targets (make-rename-transformer #'targets)] ...)
                           #,rest))))))))

  ;; A terrible binding pattern is necessary for store deltas. We /hoist/
  ;; the values that are used in join so they are in scope of the real σ.
  (define-splicing-syntax-class (join-clauses maybe-prev-σ outer-σ body)
    #:attributes (clauses (ids 1) (vs 1) (prev-σs 1))
    (pattern (~seq) #:attr clauses '() #:attr (ids 1) '() #:attr (vs 1) '()
             #:attr (prev-σs 1) '())
    (pattern (~seq (~bind [new-id (generate-temporary)])
                   (~or (~var c (comp-clauses (or maybe-prev-σ outer-σ) outer-σ body))
                        (~var join (join-clause (and σ-∆s? #'new-id)
                                                outer-σ body)))
                   (~var joins (join-clauses (attribute join.new-σ) outer-σ body)))
             #:attr clauses (cons (or (attribute join.clause)
                                      (attribute c.clause))
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
                                    (attribute joins.prev-σs))))

  (syntax-parse stx
    ;; if we don't get a store via clauses, σ is the default.
    [(_ (σ:id) (joins) body:expr)
     ;; This necessitates an order that do-targets is specified.
     ;; First store, then states
     #:declare joins (join-clauses #f #'σ #'body)

     ;; flags conflate imperative store and imperative worklist in wide case
     ;; store-passing/store-δ-accumulation is needed if
     ;; ¬wide or (¬pre-alloc and ¬imperative)
     ;; ≡ ¬(wide and (pre-alloc or imperative))
     (define binds (let loop ([j (reverse (attribute joins.clauses))]
                              [full #'(do-body-transformer body)])
                     (match j
                       [(cons fn js) (loop js (fn full))]
                       [_ full])))

     (define hoist-binds
       (if σ-∆s?
           (if global-σ?
               #'([joins.ids joins.vs] ...)
               #'([joins.ids (let ([joins.prev-σs σ]) joins.vs)] ...))
           #'()))
     (quasisyntax/loc stx
       (let #,hoist-binds #,binds))]
    [(_ (σ:id) ([x:id e:expr] ... blob ...) body:expr)
     (raise-syntax-error #f "Joins failed" stx)]))