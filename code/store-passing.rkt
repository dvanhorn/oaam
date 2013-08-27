#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "fix.rkt" "handle-limits.rkt" "ast.rkt" 
         "goedel-hash.rkt" "data.rkt"
         "graph.rkt" racket/stxparam
         racket/trace
         (for-syntax racket/syntax syntax/parse))
(provide bind-join-whole bind-join*-whole
         (for-syntax bind-rest) ;; common helper
         wide-step
         mk-set-fixpoint^
         mk-special-set-fixpoint^
         mk-special2-set-fixpoint^
         mk-special3-set-fixpoint^
         with-narrow-set-monad
         with-σ-passing-set-monad
         bind-μbump-whole
         bind-μbump*-whole
         target-hash-top-getter
         target-hash-μgetter
         with-whole-σ
         with-whole-GH-σ
         with-whole-μ)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widen set-monad fixpoint
(define-simple-macro* (wide-step-specialized step)
  (λ (state-count #,@(if (syntax-parameter-value #'generate-graph?)
                         #'(graph)
                         #'()))
     (λ (wsσ cs)
        (set-box! state-count (+ (unbox state-count) (set-count cs)))
        (define-values (σ* cs*)
          (for/fold ([σ* wsσ] [cs ∅]) ([c (in-set cs)])
            (define-values (σ** cs*) (step (cons wsσ c)))
            ;; Add new states to accumulator and construct graph
            (define cs**
              #,(if (syntax-parameter-value #'generate-graph?)
                    #'(for/set #:initial cs ([c* (in-set cs*)])
                               (add-edge! graph c c*)
                               c*)
                    #'(∪ cs cs*)))
            (values (join-store σ* σ**) cs**)))
        ;; Stuck states are the same as input. Remove stuck states from the count
        ;; XXX: Remove for performant version. This is just for statistics.
        (values σ* cs*))))

(define-simple-macro* (wide-step-specialized2 step)
  (λ (state-count #,@(if (syntax-parameter-value #'generate-graph?)
                         #'(graph)
                         #'()))
     (λ (state)
        (match state
          [(cons wsσ cs)
           (set-box! state-count (+ (unbox state-count) (set-count cs)))
           (define-values (σ* cs*)
             (for/fold ([σ* wsσ] [cs ∅]) ([c (in-set cs)])
               (define-values (σ** cs*) (step (cons wsσ c)))
               ;; Add new states to accumulator and construct graph
               (define cs**
                 #,(if (syntax-parameter-value #'generate-graph?)
                       #'(for/set #:initial cs ([c* (in-set cs*)])
                                  (add-edge! graph c c*)
                                  c*)
                       #'(∪ cs cs*)))
               (reset-kind!)
               (values (join-store σ* σ**) cs**)))
           (set (cons σ* cs*))]
          [_ (error 'wide-step-specialized2 "Wat ~a" state)]))))

(define-syntax-rule (wide-step step)
  (λ (state-count)
     (λ (state)
        (match state
          [(cons wsσ cs)
           (define initial (for/set ([c (in-set cs)]) (cons wsσ c)))
           (define-values (σ* cs*)
             (for/fold ([σ empty-σ] [cs ∅]) ([s (in-set initial)])
               (define-values (σ* cs*) (step s))
               (values (join-store σ σ*) (∪ cs cs*))))
           (set-box! state-count (+ (unbox state-count)
                                    (set-count (cs* . ∖ . cs))))
           (set (cons σ* cs*))]
          [_ (error 'wide-step "bad output ~a~%" state)]))))

(define-simple-macro* (mk-special-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     #,@(if (syntax-parameter-value #'generate-graph?)
            #'((define graph (make-hash)))
            #'())
     (define state-count* (state-count))
     (set-box! state-count* 0)
     (define step^ ((wide-step-specialized step) state-count*
                    #,@(if (syntax-parameter-value #'generate-graph?)
                           #'(graph)
                           #'())))
     (set-box! (start-time) (current-milliseconds))
     (define-values (Σ ss) (fix-t step^ f^σ cs))
     (state-rate)
     (define final-cs
       (for/fold ([final-cs ∅]) ([s ss])
         (match s
           [(cons fsσ c)
            (values (∪1 final-cs c))]
           [_ (error 'name "bad output ~a~%" s)])))
     ;; filter the final results
     (values (format "State count: ~a" (unbox state-count*))
             (format "Point count: ~a" (set-count final-cs))
             (car Σ)
             (for/set ([c (in-set final-cs)]
                       #:when (ans^? c))
               c)))))

(define-syntax (mk-special2-set-fixpoint^ stx)
  (syntax-parse stx
    [(_ fix name ans^ ev co compiled?)
     (with-syntax ([ev? (format-id #'ev "~a?" #'ev)]
                   [ev-e (format-id #'ev "~a-e" #'ev)]
                   [co? (format-id #'co "~a?" #'co)]
                   [ans^? (format-id #'ans^ "~a?" #'ans^)]
                   [ans^-τ (format-id #'ans^ "~a-τ" #'ans^)])
       #`(define-syntax-rule (name step fst)
           (let ()
             (define-values (f^σ cs) fst)
             #,@(if (syntax-parameter-value #'generate-graph?)
                    #'((define graph (make-hash)))
                    #'())
             (define state-count* (state-count))
             (set-box! state-count* 0)
             (define step^ ((wide-step-specialized2 step) state-count*
                            #,@(if (syntax-parameter-value #'generate-graph?)
                                   #'(graph)
                                   #'())))
             #,@(if (syntax-e #'compiled?)
                    #'((define (ev? s) #f) ;; added for compiled
                       (define (ev-e s) #f))
                    #'())
             (define (ev-var? s)
               (and (ev? s) (var? (ev-e s))))
             (set-box! (start-time) (current-milliseconds))
             (define ss (fix step^ (set (cons f^σ cs))))
             (printf "Fixed~%")
             (define-values (last-σ final-cs)
               (for/fold ([last-σ f^σ] [final-cs ∅])
                   ([s (in-set ss)])
                 (match s
                   [(cons σ cs) (values (join-store last-σ σ) (∪ final-cs cs))]
                   [_ (error 'special "Wat ~a" s)])))
             (state-rate)
             #,@(if-graph #'(dump-dot graph ev-var? ev? co? compiled?))
             ;; filter the final results
             (values (format "State count: ~a" (unbox state-count*))
                     (format "Point count: ~a" (set-count final-cs))
                     last-σ
                     (for/set ([c (in-set final-cs)]
                               #:when (ans^? c))
                       c)))))]))

;; Uses counting and merges stores between stepping all states.
(define-syntax-rule (mk-special3-set-fixpoint^ name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define state-count* (state-count))
     (set-box! state-count* 0)
     (set-box! (start-time) (current-milliseconds))
     (define-values (σ final-cs)
       (let loop ([accum (hash)] [front cs] [σ f^σ] [σ-count 0])
           (match (for/first ([c (in-set front)]) c)
             [#f 
              (state-rate)
              (values σ (for/set ([(c _) (in-hash accum)]) c))]
             [c
              (set-box! state-count* (add1 (unbox state-count)))
              (define-values (σ* cs*) (step (cons σ c)))
              (define count* (if (equal? σ σ*) σ-count (add1 σ-count)))
              (define-values (accum* front*)
                (for/fold ([accum accum] [front (front . ∖1 . c)])
                    ([c* (in-set cs*)]
                     #:unless (= count* (hash-ref accum c* -1)))
                  (values (hash-set accum c* count*) (∪1 front c*))))
              (loop accum* front* σ* count*)])))
     ;; filter the final results
     (values (format "State count: ~a" (unbox state-count*))
             (format "Point count: ~a" (set-count final-cs))
             σ
             (for/set ([c (in-set final-cs)]
                       #:when (ans^? c))
               c)))))

(define-syntax-rule (mk-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define state-count* (state-count))
     (set-box! state-count* 0)
     (define step^ ((wide-step step) state-count*))
     (set-box! (start-time) (current-milliseconds))
     (define ss (fix step^ (set (cons f^σ cs))))
     (state-rate)
     (define-values (last-σ final-cs)
       (for/fold ([last-σ empty-σ] [final-cs ∅]) ([s ss])
         (match s
           [(cons fsσ cs)
            (values (join-store last-σ fsσ)
                    (for/set #:initial final-cs ([c (in-set cs)]
                                                 #:when (ans^? c))
                             c))]
           [_ (error 'name "bad output ~a~%" s)])))
     (values (format "State count: ~a" (unbox state-count*))
             (format "Point count: ~a" (set-count (for/union ([p (in-set ss)]) (cdr p))))
             last-σ final-cs))))

(define-for-syntax do-body-transform-σ/cs
  (syntax-rules () [(_ e) (let-values ([(σ* cs) e])
                            #;
                            (log-debug "Transformed ~a ~a" cs target-cs)
                            (values σ* (∪ target-cs cs)))]))
(define-for-syntax do-body-transform-cs
  (syntax-rules () [(_ e) (let ([cs e]) (∪ target-cs cs))]))

(define-for-syntax (bind-rest inner-σ body)
  #`(syntax-parameterize ([target-σ (make-rename-transformer #'#,inner-σ)])
      #,body))
(define-simple-macro* (bind-join-whole (a vs) body)
  (let ([σjoin (join target-σ a vs)]) #,(bind-rest #'σjoin #'body)))
(define-simple-macro* (bind-join*-whole (as vss) body)
  (let ([σjoin* (join* target-σ as vss)])
    (bind-μbump* (as)
     #,(bind-rest #'σjoin* #'body))))

(define ((σ-getter origin) hgσ a)
  (unless (σ? hgσ) (error origin "bad store ~a" hgσ))
  ;; XXX: Unsoundness in GC leads to error?
  (σ-ref hgσ a ∅ #;(λ () (error origin "Unbound address ~a in store ~a" a hgσ))
            ))
(define-syntax-rule (mk-target-getter name target getter)
  (define-syntax (name stx)
    (syntax-case stx ()
      [(_ a) #'(getter target a)]
      [_ #'(λ (a) (getter target a))])))
(mk-target-getter target-hash-top-getter top-σ (σ-getter 'top))
(mk-target-getter target-hash-getter target-σ (σ-getter 'σ))
(define-syntax (target-hash-μgetter stx)
  (syntax-case stx ()
    [(_ a) #'(hash-ref target-μ a 0)]
    [_ #'(λ (a) (hash-ref target-μ a))]))

(define-syntax-rule (with-σ-passing-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (values target-σ (∪1 target-cs e))])]
    [do-body-transformer do-body-transform-σ/cs])
   body))

(define-syntax-rule (with-narrow-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (∪1 target-cs e)])]
    [do-body-transformer do-body-transform-cs])
   body))

(define-simple-macro* (bind-μbump-whole (a) . body)
  #,(if-μ #'(let ([μ* (hash-set target-μ a (μinc (μgetter a)))])
              (syntax-parameterize ([target-μ (make-rename-transformer #'μ*)])
                . body))
          #'(let () . body)))

(define-simple-macro* (bind-μbump*-whole (as) . body)
  #,(if-μ #'(let ([μ* (for/fold ([μ target-μ]) ([a (in-list as)])
                        (hash-set μ a (μinc (hash-ref μ a 0))))])
              (syntax-parameterize ([target-μ (make-rename-transformer #'μ*)])
                . body))
          #'(let () . body)))

(define-syntax-rule (with-whole-μ . body)
  (splicing-syntax-parameterize
   ([bind-μbump (make-rename-transformer #'bind-μbump-whole)]
    [bind-μbump* (make-rename-transformer #'bind-μbump*-whole)]
    [μgetter (make-rename-transformer #'target-hash-μgetter)])
   . body))

(define-syntax-rule (with-whole-σ . body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-whole)]
    [bind-join* (make-rename-transformer #'bind-join*-whole)]
    [getter (make-rename-transformer #'target-hash-getter)])
   (with-whole-μ . body)))

(define-syntax-rule (with-whole-GH-σ . body)
  (splicing-syntax-parameterize
   ([empty-σ (make-rename-transformer #'empty-GH-hash)]
    [Gödel? #t])
   (with-whole-σ . body)))