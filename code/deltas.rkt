#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "store-passing.rkt" "context.rkt" "fix.rkt" "parameters.rkt"
         "handle-limits.rkt"
         "graph.rkt" racket/stxparam)
(provide bind-join-∆s
         #;bind-join*-∆s
         mk-∆-fix^ mk-timestamp-∆-fix^ with-σ-∆s)

;; Utility function for combining multiple σ-∆s
(define (map2-append f acc ls0 ls1)
  (let loop ([ls0 ls0] [ls1 ls1])
    (match* (ls0 ls1)
      [((cons h0 t0) (cons h1 t1))
       (cons (f h0 h1) (loop t0 t1))]
      [('() '()) acc]
      [(_ _)
       (error 'map2-append "Expected same length lists. Finished at ~a ~a"
              ls0 ls1)])))

(define-simple-macro* (bind-join-∆s (∆s* ∆s a vs) body)
  (let ([∆s* (cons (cons a vs) ∆s)]) #,(bind-help #'∆s* #'body)))
#;
(define-simple-macro* (bind-join*-∆s (∆s* ∆s as vss) body)
  (let ([∆s* (map2-append cons ∆s as vss)]) #,(bind-help #'∆s* #'body)))

(define-syntax-rule (top-hash-getter thgσ a)
  (hash-ref top-σ a (λ () (error 'top-hash-getter "Unbound address ~a in store ~a" a top-σ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Wide fixpoint for σ-∆s

(define-syntax-rule (∆-step step)
  (λ (state-count)
     (λ (state)
        (match state
          [(cons σ cs)
           (define-values (∆ cs*)
             (for/fold ([∆ '()] [cs* ∅]) ([c (in-set cs)])
               (define-values (∆* cs**) (step (cons σ c)))
               (values (append ∆* ∆) (∪ cs** cs*))))
           (set-box! state-count (+ (unbox state-count)
                                    (set-count (cs* . ∖ . cs))))
           (set (cons (update ∆ σ) cs*))]))))

(define-syntax-rule (mk-∆-fix^ name ans^?)
  (define-syntax-rule (name step fst)
    (let-values ([(∆ cs) fst])
      (define state-count* (state-count))
      (set-box! state-count* 0)
      (define step^ ((∆-step step) state-count*))
      (set-box! (start-time) (current-milliseconds))
      (define ss (fix step^ (set (cons (update ∆ (hash)) cs))))
      (state-rate)
      (define-values (last-σ final-cs)
        (for/fold ([last-σ (hash)] [final-cs ∅]) ([s ss])
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

;; Uses counting and merges stores between stepping all states.
(define-simple-macro* (mk-timestamp-∆-fix^ name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (set-box! (start-time) (current-milliseconds))
     (define state-count* (state-count))
     (set-box! state-count* 0)
     #,@(when-graph #'(define graph (new-graph)))
     (define-values (∆ cs) fst)
     (define-values (last-σ final-cs)
       (let loop ([accum (hash)] [front cs] [σ (update ∆ (hash))] [σ-count 0])
         (cond [(∅? front)
                (state-rate)
                #,@(when-graph #'(dump-dot graph))
                (values σ (for/set ([(c _) (in-hash accum)]) c))]
               [else
                ;; If a state is revisited with a different store, that counts as
                ;; a different state.
                (set-box! state-count* (+ (unbox state-count*) (set-count front)))
                (let step/join ([accum accum] [todo front] [front ∅] [∆ '()])
                  (match (for/first ([c (in-set todo)]) c)
                    [#f (define σ* (update ∆ σ))
                        (define count* (if (null? ∆) σ-count (add1 σ-count)))
                        (loop accum front σ* count*)]
                    [c (define-values (∆* cs*) (step (cons σ c)))
                       (define change? (would-update? ∆* σ))
                       (define ∆** (if change? (append ∆* ∆) ∆))
                       (define todo* (todo . ∖1 . c))
                       (define-values (accum* front*)
                         (for/fold ([accum* accum] [front* front])
                             ([c* (in-set cs*)]
                              #:when (or change?
                                         (not (= σ-count (hash-ref accum c* -1)))))
                           #,@(when-graph #'(add-edge! graph c c*))
                           (values (hash-set accum* c* σ-count) (∪1 front* c*))))
                       (step/join accum* todo* front* ∆**)]))])))
     ;; filter the final results
     (values (format "State count: ~a" (unbox state-count*))
             (format "Point count: ~a" (set-count final-cs))
             last-σ
             (for/set ([c (in-set final-cs)]
                       #:when (ans^? c))
               c)))))

(define-syntax-parameter top-σ #f)
;; We need this to initialize before target-σ, so we need
;; a keyword that is less than #:σ. Luckily, #:top-σ is.
(define-syntax initialize-top-σ
  (syntax-rules () [(_ body ...)
                    (let ([tσ target-σ])
                      (syntax-parameterize ([top-σ (make-rename-transformer #'tσ)])
                        body ...))]))
(define-syntax initialize-∆s
  (syntax-rules () [(_ body ...)
                    (let ([∆s '()])
                      (syntax-parameterize ([target-σ (make-rename-transformer #'∆s)])
                        body ...))]))
(define-for-syntax top-σ-target
  (target #'top-σ '#:top-σ (make-rename-transformer #'initialize-top-σ)))
(define-for-syntax ∆s-target
  (target #'target-σ '#:σ (make-rename-transformer #'initialize-∆s)))

(define-syntax-rule (with-σ-∆s body)
  (splicing-syntax-parameterize
      ([av-targets (cons top-σ-target (syntax-parameter-value #'av-targets))]
       [st-targets (cons ∆s-target (syntax-parameter-value #'st-targets))]
       [bind-join (make-rename-transformer #'bind-join-∆s)]
#;
       [bind-join* (make-rename-transformer #'bind-join*-∆s)]
       [getter (make-rename-transformer #'top-hash-getter)])
   body))
