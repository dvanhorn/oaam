#lang racket
(require (for-syntax syntax/parse racket/syntax racket/list racket/dict
                     (except-in racket/match match match*)
                     "notation.rkt")
         racket/stxparam "notation.rkt" "data.rkt" "parameters.rkt"
         racket/generator)
(provide continue do-comp expect-do-values
         ;; derived forms.
         bind-alias bind-alias* bind-big-alias bind-join*
         ;; default forms.
         bind-join-local
         bind-get-kont
         bind-push
         ;; for do-managed accumulators
         do-comp do-values
         do-body-transformer
         (for-syntax mk-do listy with-do-binds))

;; Helper for building targets
(define-for-syntax (listy x) (if x (list x) '()))

(mk-syntax-parameters do do-extra-values)
;; Private parameters
(define-syntax-parameter alloc-ctx? #f)
(define-syntax-parameter cr-ctx '())
(define-syntax-parameter in-do-ctx? #f)
(define-syntax-rule (with-do body ...)
  (syntax-parameterize ([in-do-ctx? #t]) body ...))

(define-syntax (do-values stx)
  (syntax-parse stx
    [(_ . args)
     (define current-cr-ctx (syntax-parameter-value #'cr-ctx))
     (define cr-given
       (filter (λ (t) (or (eq? 'all current-cr-ctx)
                          (memq (target-kw t) current-cr-ctx)))
               (syntax-parameter-value #'cr-targets)))
     (define add-al? (syntax-parameter-value #'alloc-ctx?))
     (define targets
       (sort (append (syntax-parameter-value #'st-targets)
                     (if add-al? (syntax-parameter-value #'al-targets) '())
                     cr-given)
             target<=?))
     (unless (let ([c (syntax-parameter-value #'do-extra-values)]
                   [num (length (syntax->list #'args))])
               (if c (= c num) (zero? num)))
       (raise-syntax-error #f "Too few values" stx))
     (define tkws (map target-kw targets))
     #`(values #,@(map target-param targets) . args)]))
(define-syntax-rule (continue) (do-values))

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

;; default: do nothing to the body of a do.
(define-syntax-parameter do-body-transformer
  (λ (stx) (syntax-case stx () [(_ e) #'e #;
                                (with-do-binds extra
                                        #'(do-comp #:bind (#:σ σ extra ...) e
                                                   (do-values extra ...)))])))

;; for tandem analysis. default: bind nothing
(define-syntax-parameter bind-extra
  (syntax-rules () [(_ ids body ...) (let () body ...)]))
(define-syntax-parameter bind-extra-prim
  (syntax-rules () [(_ ids body ...) (let () body ...)]))
(define-syntax-parameter bind-extra-initial
  (syntax-rules () [(_ body ...) (let () body ...)]))
(provide bind-extra bind-extra-initial bind-extra-prim)
;; regular vs pushdown. Default: regular
(define-syntax-parameter bind-push
  (syntax-rules ()
    [(_ (σ* a* bpσ l δ k) body)
     (let ([a* (make-var-contour l δ)])
       (bind-join (σ* bpσ a* (singleton k)) body))]))
(define-syntax-parameter bind-get-kont (make-rename-transformer #'bind-get))
(define-syntax-parameter bind-join-local (make-rename-transformer #'bind-join))

;; Derived forms for convenience
(define-syntax-rule (bind-alias (σ* σ alias to-alias) body)
  (bind-get (res σ to-alias) (bind-join (σ* σ alias res) body)))

(define-syntax-rule (bind-join* (σ* σ as vss) body)
  (do-comp #:bind/extra (#:σ σ*)
           (do (σ) loop ([-as as] [-vss vss])
               (match* (-as -vss)
                 [('() '()) (continue)]
                 [((cons a -as) (cons vs -vss))
                  (bind-join (σ* σ a vs) (loop σ* -as -vss))]
                 [(_ _) (error 'bind-join* "Bad match ~a ~a" -as -vss)]))
           body))

(define-syntax-rule (bind-alias* (σ* σ aliases all-to-alias) body)
  (do-comp #:bind/extra (#:σ σ*)
           (do (σ) loop ([-aliases aliases] [-all-to-alias all-to-alias])
               (log-debug "Bind alias ~a ~a" -aliases -all-to-alias)
               (match* (-aliases -all-to-alias)
                 [('() '()) (continue)]
                 [((cons alias -aliases) (cons to-alias -all-to-alias))
                  (bind-alias (σ* σ alias to-alias) (loop σ* -aliases -all-to-alias))]
                 [(_ _) (error 'bind-alias* "Bad match ~a ~a" -aliases -all-to-alias)]))
           body))

(define-syntax-rule (bind-big-alias (σ* σ alias all-to-alias) body)
  (do-comp #:bind (#:σ σi acc)
           (do (σ) loop ([-all-to-alias all-to-alias] [acc nothing])
               (match -all-to-alias
                 ['() (do-values acc)]
                 [(cons to-alias -all-to-alias)
                  (bind-get (res σ to-alias)
                    (loop σ -all-to-alias (⊓ acc res)))]))
           (bind-join (σ* σi alias acc) body)))

;; Sometimes we need to factor out the body of a do form. To avoid
;; code duplication, we lift to a lambda, but add in the identifiers that
;; the do form hides.

;; Compose do forms
(define-syntax (do-comp stx)
  (syntax-parse stx
    [(_ (~or (~optional (~seq (~or (~and #:bind
                                    (~bind [extra? #f]
                                           [targs (get-st)]
                                           [ftargs (get-stcr)]))
                              (~and #:bind/extra
                                    (~bind [extra? #t]
                                           [targs (get-stalcr)]
                                           [ftargs (get-stalcr)])))
                         (~var f (formals (attribute ftargs) (not (attribute extra?))))))
             (~optional (~seq #:wrap wrapper:id))) ...
        e:expr e1)
     ;; Sometimes we need to extend the store but not extras.
     ;; In the narrow case, the store is in al-targets, not st-targets
     (define crs (get-cr))
     (define given-cr-ctx
       (and (not (attribute extra?)) ;; Carry regardless of mention if bind/extra
            #:bind fkws (attribute f.kws)            
            #:bind crkws (for/list ([t (in-list crs)]
                                    #:when (memq (target-kw t) fkws))
                           (target-kw t))
            (pair? crkws)
            crkws))

     (define use-targs
       (if given-cr-ctx
           (for/list ([t (in-list (attribute ftargs))]
                      #:when (or (memq (target-kw t) given-cr-ctx)
                                 (not (memq t crs))))
             t)
           (attribute targs)))
     (define extra (syntax-parameter-value #'do-extra-values))

     (with-syntax* ([(acc-p ...) (map target-param use-targs)]
                    [(acc-ids ...)
                     (cond
                      [(attribute f) #'(f.kw-ids ...)]
                      [else (generate-temporaries #'(acc-p ...))])]
                    [(bind ...)
                     (cond
                      [(attribute f) #'(f.ids ...)]
                      [else (with-do-binds extra #'(extra ...))])])

       (define tr
         (syntax-parser
           [(_ (~var a (actuals use-targs)))
            (with-syntax
                ([((targ id) ...)
                  (for/list ([t (in-list use-targs)]
                             [id (in-list (syntax->list #'(acc-ids ...)))])
                    (list (target-param t)
                          (or (dict-ref (attribute a.kw-exprs) (target-kw t) #f)
                              id)))])              
              (quasisyntax/loc stx
                (syntax-parameterize ([targ (make-rename-transformer #'id)] ...)
                  a.exprs ...)))]))

       (exn-wrap stx
        (quasisyntax/loc stx
          (let-values ([(acc-ids ... bind ...)
                        (expect-do-values
                            #:values #,(length (syntax->list #'(bind ...)))
                          #,@(listy (and (attribute extra?) #'#:extra))
                          #,@(if given-cr-ctx
                                 #`(#:carry #,given-cr-ctx)
                                 '())                          
                          e)])
            #,(if (attribute wrapper)
                  #`(let-syntax ([wrapper #,tr])
                      e1)
                  (tr #'(wrap e1)))))))]))

(define-simple-macro* (expect-do-values (~or (~optional (~seq #:values num:nat))
                                             (~optional (~and #:extra (~bind [extra? #t]))
                                                        #:defaults ([extra? #f]))
                                             (~optional (~seq #:carry (kws:keyword ...)))) ...
                                        body:expr ...)
  (syntax-parameterize (#,@(listy (and (attribute num) #'[do-extra-values (syntax-e #'num)]))
                        #,@(if (and (attribute extra?))
                               #'([alloc-ctx? #t]
                                  [cr-ctx 'all])
                               #'())
                        #,@(listy (and (not (attribute extra?))
                                       (attribute kws)
                                       #`[cr-ctx '#,(syntax->datum #'(kws ...))])))
    body ...))

(define-for-syntax ((mk-do generators?) stx)
  ;; Construct the values tuple given the previously bound σ and cs
  (define in-do? (syntax-parameter-value #'in-do-ctx?))
  (define extra? (syntax-parameter-value #'alloc-ctx?))
  (define stalcr (get-stalcr))
  (define st* (if extra? stalcr (get-st)))
  (define bind-σ? (kw-in-target '#:σ st*))
  (define bind-σ-loop? (kw-in-target '#:σ stalcr))

  (define gen-wrap
    (cond [(or in-do? (not generators?)) values]
          [(null? st*) (λ (stx) #`(begin #,stx 'done))]
          [else (λ (stx) #`(begin (yield #,stx) 'done))]))
  (define add-0val? (and (null? st*)
                         (let ([xn (syntax-parameter-value #'do-extra-values)])
                           (if xn (zero? xn) #t))))
  (define-splicing-syntax-class acc-clauses
    #:attributes ((clauses 1))
    (pattern (~seq #:accumulate (~and ([acc-ids:id acc-init:expr ...])
                                      (clauses ...)))))
  (define-syntax-class (join-clause maybe-accumulators)
    #:attributes (clause new-σ keep-accs?)
    (pattern [σ*:id (~or (~and #:join (~bind [bindf #'bind-join]))
                         (~and #:join* (~bind [bindf #'bind-join*]))
                         (~and #:alias (~bind [bindf #'bind-alias]))
                         (~and #:alias* (~bind [bindf #'bind-alias*]))) jσ:expr a:expr vs:expr]
             #:with new-σ #'σ*
             #:attr keep-accs? #f
             #:attr clause
             (λ (rest) #`(bindf (σ* jσ a vs) #,rest)))
    (pattern [res:id (~or (~and #:get (~bind [bindf #'bind-get]))
                          (~and #:get-kont (~bind [bindf #'bind-get-kont]))
                          (~and #:force (~bind [bindf #'bind-force]))
                          (~and #:delay (~bind [bindf #'bind-delay]))) jσ:expr a:expr]
             #:with new-σ #'jσ ;; XXX: not new
             #:attr keep-accs? #f
             #:attr clause (λ (rest) #`(bindf (res jσ a) #,rest)))
    (pattern [(ρ* σ* δ*) #:bind ρ bσ l δ xs vs]
             #:with new-σ #'σ*
             #:attr keep-accs? #f
             #:attr clause
             (λ (rest) #`(bind (ρ* σ* δ*) (ρ bσ l δ xs vs) #,rest)))
    (pattern [(ρ* σ* δ*) (~or (~and #:bind-rest (~bind [bindf #'bind-rest]))
                              (~and #:bind-rest-apply (~bind [bindf #'bind-rest-apply])))
              ρ brσ l δ xs r vs]
             #:with new-σ #'σ*
             #:attr keep-accs? #f
             #:attr clause
             (λ (rest) #`(bindf (ρ* σ* δ*) (ρ brσ l δ xs r vs) #,rest)))
    (pattern [(σ*:id a*:id) #:push bpσ l δ k]
             #:with new-σ #'σ*
             #:attr keep-accs? #f
             #:attr clause
             (λ (rest) #`(bind-push (σ* a* bpσ l δ k) #,rest)))
    ;; a couple shorthands
    (pattern [σ*:id (~or (~and #:join-forcing (~bind [bindf #'bind-join]))
                         (~and #:join-local-forcing (~bind [bindf #'bind-join-local])))
                    jσ:expr a:expr v:expr]
             #:with new-σ #'σ*
             #:attr keep-accs? #f
             #:attr clause
             (λ (rest) #`(do (jσ) ([fs #:force jσ v])
                           (bindf (σ* jσ a fs) #,rest))))
    (pattern [res:id (~or (~and #:in-get (~bind [bindf #'bind-get]))
                          (~and #:in-kont (~bind [bindf #'bind-get-kont]))
                          (~and #:in-force (~bind [bindf #'bind-force]))
                          (~and #:in-delay (~bind [bindf #'bind-delay]))) jσ:expr a:expr]
             #:with new-σ #'jσ ;; XXX: not new
             #:attr keep-accs? #f
             #:attr clause (λ (rest) #`(bindf (res-tmp jσ a)
                                         (do (jσ)
                                             #,@(if maybe-accumulators
                                                    #`(#:accumulate #,maybe-accumulators)
                                                    '())
                                           ([res (in-set res-tmp)])
                                           #,rest)))))

  (define-splicing-syntax-class (join-clauses maybe-prev-σ maybe-accumulators)
    #:attributes (clauses last-σ)
    (pattern (~seq (~var join (join-clause maybe-accumulators))
                   (~var joins (join-clauses (attribute join.new-σ)
                                             (and (attribute join.keep-accs?)
                                                  maybe-accumulators))))
             #:attr clauses (cons (attribute join.clause)
                                  (attribute joins.clauses))
             #:attr last-σ (attribute joins.last-σ))
    (pattern (~seq) #:attr clauses '()
             #:attr last-σ maybe-prev-σ
             #:fail-unless maybe-prev-σ "Expected at least one join clause"))

  (syntax-parse stx
    [(_ (cσ:id) (~optional a:acc-clauses)
        (c:comp-clauses clauses ...) body:expr ...+)
     ;; build a new fold or a fold that continues adding to the
     ;; outer do's targets. σ is bound to itelf since the body may
     ;; still refer to it. cs go to a new identifier.
     (define no-σ-st* (remove-kw-target '#:σ st*))
     (define no-σ-st*-params (map target-param no-σ-st*))
     (with-syntax ([(σ-id ...) (listy (and bind-σ? (generate-temporary #'σ)))]
                   [(σ-acc ...) (listy (and bind-σ? #'target-σ))]
                   [(accs ...) no-σ-st*-params]
                   [(acc-ids ...) (generate-temporaries no-σ-st*-params)]
                   [(g gs ...) #'(c.guards ...)]                   
                   [((bind bind-init) ...)
                    (or (attribute a.clauses)                        
                        (let ([lst (syntax->list (with-do-binds extra #'(extra ...)))])
                          (map (λ (v) (list v #f)) lst)))])
       (gen-wrap
        (exn-wrap stx
        #`(for/fold ([σ-id σ-acc] ... 
                     [acc-ids accs] ...
                     [bind bind-init] ...) (g)
            (syntax-parameterize ([σ-acc (make-rename-transformer #'σ-id)] ...
                                  [accs (make-rename-transformer #'acc-ids)] ...
                                  #,@(listy (and #:bind c (attribute a.clauses)
                                                 #`[do-extra-values #,(length c)])))
              (let ([cσ σ-id] ...)
                (for*/fold ([σ-id σ-id] ...
                            [acc-ids acc-ids] ...
                            [bind bind] ...)
                    (gs ...)
                  (let ([cσ σ-id] ...)
                    (do-body-transformer
                     (do (cσ) (clauses ...) body ...))))))))))]
    
    ;; if we don't get a store via clauses, σ is the default.
    [(_ (jσ:id) (~optional a:acc-clauses)
        ((~var joins (join-clauses #f (attribute a.clauses))) clauses ...)
        body:expr ...+)
     (define join-body
       #`(do (#,(attribute joins.last-σ)) (clauses ...)
           (do-body-transformer (with-do body ...))))
     (define binds
       (exn-wrap
        stx
        #`(initialize-targets
           (syntax-parameterize ([target-σ (make-rename-transformer #'jσ)])
             #,(for/fold ([full join-body])
                   ([fn (in-list (reverse (attribute joins.clauses)))])
                 (fn full))))))
     (gen-wrap binds)]

    [(_ (dbσ:id) () body:expr ...+)
     (exn-wrap stx
     #`(initialize-targets
        (syntax-parameterize ([target-σ (make-rename-transformer #'dbσ)])
          #,(gen-wrap
             #`(do-body-transformer
                (with-do body ... ;;#,@(listy (and add-0val? #'(values)))
                         ))))))]

    ;; when fold/fold doesn't cut it, we need a safe way to recur.
    [(_ (ℓσ:id) loop:id ([args:id arg0:expr] ...)
        (~optional (~seq (~or (~and #:values (~bind [add-extra? #f]))
                              (~and #:values/extra (~bind [add-extra? #t])))
                         num-results:nat))
        body:expr ...+)
     (define no-σ-stalcr (remove-kw-target '#:σ stalcr))
     (define no-σ-stalcr-params (map target-param no-σ-stalcr))
     (with-syntax ([(argps ...) (generate-temporaries #'(args ...))]
                   [(σ-id ...) (listy (and bind-σ-loop? (generate-temporary #'σ)))]
                   [(σ-acc ...) (listy (and bind-σ-loop? #'target-σ))]
                   [(accs ...) no-σ-stalcr-params]
                   [(acc-ids ...) (generate-temporaries no-σ-stalcr-params)])       
       (exn-wrap stx
        #`(initialize-targets
          (let real-loop ([σ-id σ-acc] ...
                          [acc-ids accs] ...
                          [args arg0] ...)
            (let ([ℓσ σ-id] ...)
              (syntax-parameterize ([σ-acc (make-rename-transformer #'σ-id)] ...
                                    [accs (make-rename-transformer #'acc-ids)] ...)
                (expect-do-values #,@(append (if (attribute num-results)
                                                 (list #'#:values #'num-results)
                                                 '())
                                             (listy (and (attribute add-extra?) #'#:extra)))
                    ;; make calling the loop seemless.
                    ;; Pass the accumulators if they exist.
                    (let-syntax ([loop (syntax-rules ()
                                         [(_ σ* argps ...)
                                          (real-loop #,@(listy (and bind-σ-loop? #'σ*))
                                                     accs ...
                                                     argps ...)])])
                      (with-do body ...)))))))))]))
