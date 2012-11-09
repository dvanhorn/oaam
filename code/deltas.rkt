#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "store-passing.rkt" "context.rkt" "fix.rkt"
         "handle-limits.rkt")
(provide bind-join-∆s bind-join*-∆s mk-∆-fix^ mk-timestamp-∆-fix^ with-σ-∆s)

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
  (let ([∆s* (cons (cons a vs) ∆s)]) #,(bind-rest #'∆s* #'body)))
(define-simple-macro* (bind-join*-∆s (∆s* ∆s as vss) body)
  (let ([∆s* (map2-append cons ∆s as vss)]) #,(bind-rest #'∆s* #'body)))

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
      (define state-count (box 0))
      (define step^ ((∆-step step) state-count))
      (define start-time (current-milliseconds))
      (define-values (ss states)
        (with-limit-handler (start-time state-count)
          (fix step^ (set (cons (update ∆ (hash)) cs)))))
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

;; Uses counting and merges stores between stepping all states.
(define-syntax-rule (mk-timestamp-∆-fix^ name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (∆ cs) fst)
     (define num-states 0)
     (define start-time (current-milliseconds))
     (define-values (last-σ final-cs)
       (with-limit-handler (start-time num-states)
         (let loop ([accum (hash)] [front cs] [σ (update ∆ (hash))] [σ-count 0])
           (match (for/first ([c (in-set front)]) c)
             [#f 
              (state-rate start-time num-states)
              (values σ (for/set ([(c _) (in-hash accum)]) c))]
             [c
              ;; If a state is revisited with a different store, that counts as
              ;; a different state.
              (set! num-states (add1 num-states))
              (define-values (∆ cs*) (step (cons σ c)))
              (define-values (σ* same?) (update/change ∆ σ))
              (define count* (if same? σ-count (add1 σ-count)))
              (define-values (accum* front*)
                (for/fold ([accum accum] [front (front . ∖1 . c)])
                    ([c* (in-set cs*)]
                     #:unless (= count* (hash-ref accum c* -1)))
                  (values (hash-set accum c* count*) (∪1 front c*))))
              (loop accum* front* σ* count*)]))))
     ;; filter the final results
     (values (format "State count: ~a" num-states)
             (format "Point count: ~a" (set-count final-cs))
             σ
             (for/set ([c (in-set final-cs)]
                       #:when (ans^? c))
               c)))))

(define-syntax-rule (with-σ-∆s body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-∆s)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s)]
    [getter (make-rename-transformer #'top-hash-getter)])
   body))
