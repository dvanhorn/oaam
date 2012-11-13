#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "fix.rkt" "handle-limits.rkt"
         "graph.rkt")
(provide bind-join-whole bind-join*-whole
         (for-syntax bind-rest) ;; common helper
         wide-step hash-getter
         mk-set-fixpoint^
         mk-special-set-fixpoint^
         mk-special2-set-fixpoint^
         mk-special3-set-fixpoint^
         with-narrow-set-monad
         with-σ-passing-set-monad
         with-whole-σ)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widen set-monad fixpoint
(define-syntax-rule (wide-step-specialized step)
  (λ (state-count graph) ;; Remove this for performant version
     (λ (state)
        (match state
          [(cons wsσ cs)
           (define-values (σ* cs*)
             (for/fold ([σ* wsσ] [cs ∅]) ([c (in-set cs)])
               (define-values (σ** cs*) (step (cons wsσ c)))
               ;; Add new states to accumulator and construct graph
               (define cs** (for/set #:initial cs ([c* (in-set cs*)])
                                     (add-edge! graph c c*)
                                     c*))
               (values (join-store σ* σ**) cs**)))
           ;; Stuck states are the same as input. Remove stuck states from the count
           ;; XXX: Remove for performant version. This is just for statistics.
           (set-box! state-count (+ (unbox state-count)
                               (set-count (cs* . ∖ . cs))))
           (set (cons σ* cs*))]
          [_ (error 'wide-step "bad output ~a~%" state)]))))

(define-syntax-rule (wide-step step)
  (λ (state-count)
     (λ (state)
        (match state
          [(cons wsσ cs)
           (define initial (for/set ([c (in-set cs)]) (cons wsσ c)))
           (define-values (σ* cs*)
             (for/fold ([σ (hash)] [cs ∅]) ([s (in-set initial)])
               (define-values (σ* cs*) (step s))
               (values (join-store σ σ*) (∪ cs cs*))))
           (set-box! state-count (+ (unbox state-count)
                                    (set-count (cs* . ∖ . cs))))
           (set (cons σ* cs*))]
          [_ (error 'wide-step "bad output ~a~%" state)]))))

(define-syntax-rule (mk-special-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define graph (make-hash))
     (define state-count (box 0))
     (define step^ ((wide-step-specialized step) state-count graph))
     (define start-time (current-milliseconds))
     (define ss (with-limit-handler (start-time state-count)
                  (fix step^ (set (cons f^σ cs)))))
     (state-rate start-time state-count)
     (define-values (σ final-cs)
       (for/fold ([last-σ (hash)] [final-cs ∅]) ([s ss])
         (match s
           [(cons fsσ cs)
            (dump-dot graph)
            (values (join-store last-σ fsσ) (∪ final-cs cs))]
           [_ (error 'name "bad output ~a~%" s)])))
     ;; filter the final results
     (values (format "State count: ~a" (unbox state-count))
             (format "Point count: ~a" (set-count final-cs))
             σ
             (for/set ([c (in-set final-cs)]
                       #:when (ans^? c))
               c)))))

;; stores the last seen heap for each state
(define-syntax-rule (mk-special2-set-fixpoint^ name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define state-count 0)
     (define start-time (current-milliseconds))
     (define-values (σ final-cs)
       (with-limit-handler (start-time state-count)
         (let loop ([accum (hash)] [front cs] [σ f^σ])
           (match (for/first ([c (in-set front)]) c)
             [#f 
              (state-rate start-time state-count)
              (values σ (for/set ([(c _) (in-hash accum)]) c))]
             [c
              (set! state-count (add1 state-count))
              (define-values (σ* cs*) (step (cons σ c)))
              (define-values (accum* front*)
                (for/fold ([accum* accum] [front* (front . ∖1 . c)])
                    ([c* (in-set cs*)]
                     #:unless (equal? σ* (hash-ref accum c* (hash))))                
                  (values (hash-set accum* c* σ*) (∪1 front* c*))))
              (loop accum* front* σ*)]))))
     ;; filter the final results
     (values (format "State count: ~a" state-count)
             (format "Point count: ~a" (set-count final-cs))
             σ
             (for/set ([c (in-set final-cs)]
                       #:when (ans^? c))
               c)))))

;; Uses counting and merges stores between stepping all states.
(define-syntax-rule (mk-special3-set-fixpoint^ name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define state-count 0)
     (define start-time (current-milliseconds))
     (define-values (σ final-cs)
       (with-limit-handler (start-time state-count)
         (let loop ([accum (hash)] [front cs] [σ f^σ] [σ-count 0])
           (match (for/first ([c (in-set front)]) c)
             [#f 
              (state-rate start-time state-count)
              (values σ (for/set ([(c _) (in-hash accum)]) c))]
             [c
              (set! state-count (add1 state-count))
              (define-values (σ* cs*) (step (cons σ c)))
              (define count* (if (equal? σ σ*) σ-count (add1 σ-count)))
              (define-values (accum* front*)
                (for/fold ([accum accum] [front (front . ∖1 . c)])
                    ([c* (in-set cs*)]
                     #:unless (= count* (hash-ref accum c* -1)))
                  (values (hash-set accum c* count*) (∪1 front c*))))
              (loop accum* front* σ* count*)]))))
     ;; filter the final results
     (values (format "State count: ~a" state-count)
             (format "Point count: ~a" (set-count final-cs))
             σ
             (for/set ([c (in-set final-cs)]
                       #:when (ans^? c))
               c)))))

(define-syntax-rule (mk-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define state-count (box 0))
     (define step^ ((wide-step step) state-count))
     (define start-time (current-milliseconds))
     (define ss (with-limit-handler (start-time state-count)
                  (fix step^ (set (cons f^σ cs)))))
     (state-rate start-time (unbox state-count))
     (define-values (last-σ final-cs)
       (for/fold ([last-σ (hash)] [final-cs ∅]) ([s ss])
         (match s
           [(cons fsσ cs)
            (values (join-store last-σ fsσ)
                    (for/set #:initial final-cs ([c (in-set cs)]
                                                 #:when (ans^? c))
                             c))]
           [_ (error 'name "bad output ~a~%" s)])))
     (values (format "State count: ~a" (unbox state-count))
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
(define-simple-macro* (bind-join-whole (σjoin sσ a vs) body)
  (let ([σjoin (join sσ a vs)]) #,(bind-rest #'σjoin #'body)))
(define-simple-macro* (bind-join*-whole (σjoin* sσ as vss) body)
  (let ([σjoin* (join* sσ as vss)]) #,(bind-rest #'σjoin* #'body)))

(define (hash-getter hgσ a)
  (hash-ref hgσ a (λ () (error 'getter "Unbound address ~a in store ~a" a hgσ))))

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

(define-syntax-rule (with-whole-σ body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-whole)]
    [bind-join* (make-rename-transformer #'bind-join*-whole)]
    [getter (make-rename-transformer #'hash-getter)])
   body))