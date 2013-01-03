#lang racket
(require "primitives.rkt" "data.rkt" "notation.rkt" racket/stxparam racket/splicing
         "do.rkt" "context.rkt" "deltas.rkt" "prealloc.rkt" "handle-limits.rkt"
         "parameters.rkt" "graph.rkt"
         (for-template "primitives.rkt")
         "env.rkt")
(provide mk-sparse-fixpoint with-sparse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sparse analyses accumulate actions on uses and changes of addresses.

(define E (make-hash))
(define ←E (make-hash))
(define todo #f)

(define-syntax-parameter target-actions #f)
(define-syntax-rule (initialize-actions body ...)
  (let ([actions (hasheq)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body ...)))
(define-for-syntax actions-target
  (target #'target-actions '#:actions (make-rename-transformer #'initialize-actions)))

;; Lattice of
;;   U/D
;; U     D
;;   #f
(define (⊓-action a₀ a₁)
  (cond [(eq? a₀ a₁) a₀]
        [a₀ (if a₁ 'U/D a₀)]
        [else a₁]))

(define (set-action As addr kind)
  (hash-set As addr (⊓-action kind (hash-ref As addr #f))))

(define (join-actions oldA newA)
  (for/fold ([A oldA]) ([(addr kind) (in-hash newA)])
    (set-action A addr kind)))

(define (add-edge point ctx target)
  (match (hash-ref E point #f)
    [#f (hash-set! E point (make-hash ``((,ctx . ,(set target)))))]
    [states (hash/set-add! states ctx target)]))

;; TODO
(define-syntax-rule (mk-sparse-fixpoint name ans? ans-v ans-σ touches)
  (define-syntax-rule (name step fst)
    (let ()
      (set-box! (start-time) (current-milliseconds))
      (define state-count* (state-count))
      (set-box! state-count* 0)
      (define fst-ss fst)
      (define clean-σ (mk-restrict-to-reachable hash-ref))
      (define sparse-step (mk-sparse-step step))
      (let loop ()
        (cond
         [(∅? todo)
          (state-rate)
          (define vs
            (for*/set ([(c _) (in-hash graph)]
                       #:when (ans? c))
              (list (ans-σ c) (ans-v c))))
          (values (format "State count: ~a" (unbox state-count*))
                  (clean-σ global-σ vs)
                  vs)]

         [else
          (define todo-old todo)
          (reset-todo!)
          (set-box! state-count* (+ (unbox state-count*)
                                    (set-count todo-old)))          
          (for ([c (in-set todo-old)]) (sparse-step c))
          (loop)])))))

;; TODO
(define-for-syntax (yield-narrow-sparse stx)
  (syntax-case stx ()
    [(_ e)
     #'(let ([state e]
             [actions target-actions])
         (define p (register-state state))
         ;; If stepping changed the store, or if the addresses this point
         ;; depends on changed since last interpretation, it must be
         ;; re-processed.
         (define change? (add-todo p actions))
         (cond [(or change? ∆?)
                (set-point-todo?! (node-data p) #t)
                (i:add-todo! state)]
               [else (void)]))]))

(define-syntax-rule (bind-get-sparse (res σ a) body)
  (let ([res (getter σ a)]
        [actions (set-action target-actions a 'U)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body)))

(define-syntax-rule (bind-join-sparse (σ* σ a v) body)
  (let ([actions (set-action target-actions a 'D)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      (bind-join (σ* σ a v) body))))

(define-syntax-rule (with-sparse body)
  (splicing-syntax-parameterize
   ([bind-get (make-rename-transformer #'bind-get-sparse)]
    [al-targets (cons actions-target (syntax-parameter-value #'al-targets))]
    [bind-join (make-rename-transformer #'bind-join-sparse)])
   body))
