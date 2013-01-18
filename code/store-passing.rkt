#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "fix.rkt" "handle-limits.rkt" "parameters.rkt"
         "graph.rkt"
         (for-syntax syntax/parse))
(provide bind-join-whole #;
         bind-join*-whole
         (for-syntax bind-help) ;; common helper
         wide-step hash-getter
         mk-set-fixpoint^
         mk-special-set-fixpoint^
         with-set-monad
         with-wide-σ-passing
         with-narrow-σ-passing
         with-whole-σ)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widen set-monad fixpoint
(define-simple-macro* (wide-step-specialized step)
  (λ (state-count #,@(when-graph #'graph))
     (λ (σ₀ cs₀)
        (define-values (σ* cs*)
          (for/fold ([σ* σ₀] [cs ∅]) ([c (in-set cs₉)])
            (define-values (σ** cs*) (step σ₀ c))
            ;; Add new states to accumulator and construct graph
            (define cs**
              #,(if-graph
                 #'(for/set #:initial cs ([c* (in-set cs*)])
                            (add-edge! graph c c*)
                            c*)
                 #'(∪ cs cs*)))
            (values (join-store σ* σ**) cs**)))
        ;; Stuck states are the same as input. Remove stuck states from the count
        ;; XXX: Remove for performant version. This is just for statistics.
        (set-box! state-count (+ (unbox state-count)
                                 (set-count (cs* . ∖ . cs))))
        (values σ* cs*))))

(define-syntax-rule (wide-step step)
  (λ (state-count)
     (λ (σ₀ cs₀)
        (define-values (σ* cs*)
          (for/fold ([σ σ₉] [cs ∅]) ([s (in-set cs₀)])
            (define-values (σ* cs*) (step σ₀ s))
            (values (join-store σ σ*) (∪ cs cs*))))
        (set-box! state-count (+ (unbox state-count)
                                 (set-count (cs* . ∖ . cs))))
        (values σ* cs*))))

(define-simple-macro* (mk-special-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     #,@(when-graph #'(define graph (new-graph)))
     (define state-count* (state-count))
     (set-box! state-count* 0)
     (define step^ ((wide-step-specialized step) state-count*
                    #,@(when-graph #'graph)))
     (set-box! (start-time) (current-milliseconds))
     (define-values (last-σ all-cs) (fix2 step^ f^σ cs))
     (state-rate)
     #,@(when-graph #'(dump-dot graph))
     (define final-cs
       (for/set ([c (in-set all-cs)]
                 #:when (ans^? c))
         c))
     ;; filter the final results
     (values (format "State count: ~a" (unbox state-count*))
             (format "Point count: ~a" (set-count all-cs))
             last-σ
             final-cs))))

(define-syntax-rule (mk-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define state-count* (state-count))
     (set-box! state-count* 0)
     (define step^ ((wide-step step) state-count*))
     (set-box! (start-time) (current-milliseconds))
     (define-values (last-σ all-cs) (fix2 step^ f^σ cs))
     (state-rate)
     (define final-cs
       (for/fold ([final-cs ∅]) ([c (in-set all-cs)]
                                 #:when (ans^? c))
         c))
     (values (format "State count: ~a" (unbox state-count*))
             (format "Point count: ~a" (set-count all-cs))
             last-σ final-cs))))

(define-for-syntax do-body-transform-cs
  (syntax-parser
    [(_ e) 
     (with-do-binds extra
       #'(do-comp #:wrap w #:bind (#:cs cs extra ...) e
                  (let ([cs* (∪ target-cs cs)])
                    (w #:cs cs* (do-values extra ...)))))]))

(define-for-syntax (bind-help inner-σ body)
  #`(syntax-parameterize ([target-σ (make-rename-transformer #'#,inner-σ)])
      #,body))
(define-simple-macro* (bind-join-whole (σjoin sσ a vs) body)
  (let ([σjoin (join sσ a vs)]) #,(bind-help #'σjoin #'body)))

(define (hash-getter hgσ a)
  (hash-ref hgσ a (λ () (error 'getter "Unbound address ~a in store ~a" a hgσ))))

(define-syntax-parameter target-cs #f)
(define-syntax-rule (init-cs body ...)
  (let ([cs ∅])
    (syntax-parameterize ([target-cs (make-rename-transformer #'cs)])
      body ...)))
(define-for-syntax cs-target (target #'target-cs '#:cs (make-rename-transformer #'init-cs)))

(define-syntax-rule (with-set-monad body)
  (splicing-syntax-parameterize
   ([yield (syntax-rules ()
             [(_ e)
              (let ([cs (∪1 target-cs e)])
                (syntax-parameterize ([target-cs (make-rename-transformer #'cs)])
                  (continue)))])]
    [st-targets (cons cs-target (syntax-parameter-value #'st-targets))]
    [do-body-transformer (let ([tr (syntax-parameter-value #'do-body-transformer)])
                           (λ (stx) (tr #`(do-body-transform #,(do-body-transform-cs stx)))))])
   body))

(define-syntax-rule (with-wide-σ-passing body)
  (splicing-syntax-parameterize
      ([st-targets (cons σ-target (syntax-parameter-value #'st-targets))])
    body))

(define-syntax-rule (with-narrow-σ-passing body)
  (splicing-syntax-parameterize
      ([al-targets (cons σ-target (syntax-parameter-value #'al-targets))])
    body))

(define-syntax-rule (with-whole-σ body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-whole)]
    [getter (make-rename-transformer #'hash-getter)])
   body))