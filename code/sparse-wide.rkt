#lang racket
(require "primitives.rkt" "data.rkt" "notation.rkt" racket/stxparam racket/splicing
         "do.rkt" "context.rkt"
         "deltas.rkt"
         "prealloc.rkt"
         "handle-limits.rkt"
         (rename-in "imperative.rkt" [add-todo! i:add-todo!])
         "env.rkt"
         racket/trace)
(provide mk-sparse^-fixpoint with-sparse^
         with-sparse-mutable-worklist
         with-0-ctx/prealloc/sparse
         prepare-sparse-wide/prealloc)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instrumented fixpoint for /widened/ step function xthat takes
;;; "big steps" when it can find reusable paths through the abstract state graph.

;; The wide story is less nuanced than the narrow one. In particular,
;; - ill-formed states are impossible
;; - "change" actions are unnecessary to track.
;; - congruence is just a difference between "last updated" timestamps.

;; - actions start at #f to distinguish "none" from "unknown"
(struct starting-point (state points actions) #:mutable #:prefab)
(struct point starting-point (skips at-unions) #:mutable #:prefab)

(define σ-history #f) ;; Stores the union count for each address's last update

(define state->point #f) ;; map states to the graph nodes
(define (register-state s)
  (hash-ref! state->point s (λ _ (point s (seteq) #f (seteq) -1))))

;; terrible global to communicate to other functions
;; (parameters have the right semantics, but too slow in a hot loop)
(define current-point #f)

;; States that are added by skipping can't be skipped.
(define must-do #f)
(define (reset-must-do!) (set! must-do ∅))

(define (join-actions oldA newA)
  (for/fold ([A oldA]) ([(addr age) (in-hash newA)])
    (hash-set A addr age)))

(define (add-todo! p actions)
  (match-define (starting-point _ ps A) current-point)
  ;; add edge to graph
  (set-point-at-unions! p unions)
  (set-starting-point-points! current-point (∪1 ps p))
  (set-starting-point-actions! current-point (if A (join-actions A actions) actions)))

(define (add-todo/skip! p)
  (match-define (point state _ _ skips _) p)
  ;; XXX: Is this really all that's needed? Do we also need to
  ;; update the union count at each state on the path?
  (set-point-at-unions! p unions)
  (set-point-skips! current-point (∪1 skips p))
  (set! must-do (∪1 must-do state)))

(define (ensure-σ-size/sparse)
  (when (= next-loc (vector-length global-σ))
    (set-global-σ! (grow-vector global-σ next-loc))
    (set! σ-history (grow-vector σ-history next-loc))))

(define-syntax-rule (get-contour-index!-0 c)
  (hash-ref! contour-table c
             (λ ()
                (begin0 next-loc
                        (ensure-σ-size/sparse)
                        (inc-next-loc!)))))

(define-syntax-rule (make-var-contour-0-prealloc/sparse x δ)
  (cond [(exact-nonnegative-integer? x) x]
        [else (get-contour-index!-0 x)]))

;; Joins don't accumulate "changed" addresses in the stored widened semantics
;; since the store fast-forwarding would be a no-op anyway.
(define-syntax-rule (bind-join!/sparse (σ* j!σ a vs) body)
  (begin (join!/sparse a vs) body))
(define-syntax-rule (bind-join*!/sparse (σ* j*!σ as vss) body)
  (begin (join*!/sparse as vss) body))

;; NOTE TO SELF: Store deltas might be able to speed up congruence calculations.
(define-for-syntax (yield-global-sparse stx)
  (syntax-case stx ()
    [(_ e) #'(let ([state e]
                   [actions target-actions])
               (define p (register-state state))
               (cond [(= unions (point-at-unions p))
                      (void)
                      #;
                      (printf "Seen ~a ~a ~a~%" actions unions (starting-point-state p))]
                     [else
                      (add-todo! p actions)
                      (i:add-todo! state)])
               actions)]))

(define (prepare-sparse-wide/prealloc parser sexp)
  (begin0 (prepare-prealloc parser sexp)
          (set! must-do ∅)
          (set! current-point (starting-point 'entry (seteq) ∅))
          (set! state->point (make-hash))
          (set! σ-history (make-vector (vector-length global-σ)))))
;; An address is consonant with a past state if its union count is smaller than
;; the union count of that state.
(define (actions-consonant? A)
  (and A
       (for/and ([(addr age) (in-hash A)])
         (= (vector-ref σ-history addr) age))))

;; Increase union count only if the abstract values have changed.
;; Also, save the union count for the modified address for future sparseness.
(define (join!/sparse a vs)
  (define prev (vector-ref global-σ a))
  (define upd (⊓ vs prev))
  (cond [(≡ prev upd)
         (void)
         #;
         (printf "No change to ~a with ~a~%" a vs)]
        [else
         (vector-set! global-σ a upd)
         (inc-unions!)
         (vector-set! σ-history a unions)]))

(define (join*!/sparse as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join!/sparse a vs)))

(define (skip-from ps)
  (define seen (make-hasheq)) ;; no intermediate allocation. eq? okay
  (let loop ([todo ps])
    (for ([p (in-set todo)]
          #:unless (and (hash-has-key? seen p)
                        #;
                        (printf "Seen (skip) ~a~%" (starting-point-state p))))
      (hash-set! seen p #t)
      (match-define (point _ pp* A _ _) p)
      (cond [(actions-consonant? A) (loop pp*)]
            [else
             #;
             (printf "Not consonant ~a.~%Skipping to (at ~a) ~a~%" A unions (starting-point-state p))
             (add-todo/skip! p)]))))

(define ((mk-sparse-step step) c)
  (set! current-point (register-state c))
  (match-define (point _ ps A _ _) current-point)
  (if (actions-consonant? A)
      (skip-from ps)
      (step c)))

(define-syntax-rule (mk-sparse^-fixpoint name ans^? ans^-v touches)
  (define-syntax-rule (name step fst)
    (let ()
      (set-box! (start-time) (current-milliseconds))
      (define state-count* (state-count))
      fst
      (define clean-σ (restrict-to-reachable/vector touches))
      (define sparse-step (mk-sparse-step step))
      (let loop ()
        (cond [(and (∅? todo) (∅? must-do)) ;; → null?
               (state-rate)
               (define vs
                 (for*/set ([(c _) (in-hash state->point)]
                            #:when (ans^? c))
                   (ans^-v c)))
               (values (format "State count: ~a" (unbox state-count*))
                       (format "Point count: ~a" (hash-count state->point))
                       (clean-σ global-σ vs)
                       vs)]
              [else
               (define todo-old todo)
               (define must-do-old must-do)
               (reset-todo!)
               (reset-must-do!)
               (set-box! state-count* (+ (unbox state-count*)
                                         (set-count todo-old)
                                         (set-count must-do-old)))
               (for ([c (in-set todo-old)]) (sparse-step c))
               (for ([c (in-set must-do-old)]) (step c))
               (loop)])))))

;; Get and force accumulate uses of addresses
(define-syntax-rule (bind-get-sparse (res σ a) body)
  (let ([res (getter σ a)]
        [actions (hash-set target-actions a unions)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body)))

;; An aliased address also counts as a use.
(define-syntax-rule (bind-big-alias-sparse (σ* σ alias all-to-alias) body)
  (let-values ([(actions val)
                (for/fold ([actions target-actions]
                           [val nothing]) ([to-alias (in-list all-to-alias)])
                  (values (hash-set actions to-alias unions)
                          (⊓ val (getter σ to-alias))))])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      (bind-join (σ* σ alias val) body))))

(define-syntax-rule (bind-alias*-sparse (σ* σ aliases all-to-alias) body)
  (let-values ([(actions rev-aliases rev-vals)
                (for/fold ([actions target-actions] [raliases '()] [vals '()])
                    ([alias (in-list aliases)]
                     [to-alias (in-list all-to-alias)])
                  (values (hash-set actions to-alias unions)
                          ;; XXX: icky intermediate lists.
                          (cons alias raliases)
                          (cons (getter σ to-alias) vals)))])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      (bind-join* (σ* σ rev-aliases rev-vals) body))))

(define-for-syntax do-body-transform-actions
  (syntax-rules () [(_ e) (let ([actions e]) (join-actions target-actions actions))]))

(define-syntax-rule (with-sparse-mutable-worklist body)
  (splicing-syntax-parameterize
   ([yield-meaning yield-global-sparse]
    [do-body-transformer do-body-transform-actions])
   body))

(define-syntax-rule (with-0-ctx/prealloc/sparse body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [bind-rest (make-rename-transformer #'bind-rest-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0-prealloc/sparse)])
   body))

(define-syntax-rule (with-sparse^ body)
  (splicing-syntax-parameterize
   ([bind-get (make-rename-transformer #'bind-get-sparse)]
    [bind-force (make-rename-transformer #'bind-force-sparse)]
    [bind-big-alias (make-rename-transformer #'bind-big-alias-sparse)]
    [bind-alias* (make-rename-transformer #'bind-alias*-sparse)]
    [bind-join (make-rename-transformer #'bind-join!/sparse)]
    [bind-join* (make-rename-transformer #'bind-join*!/sparse)]
    [getter (make-rename-transformer #'global-vector-getter)])
   body))
