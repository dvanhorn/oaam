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
(struct point starting-point (skips) #:mutable #:prefab)

(define σ-history #f) ;; Stores the union count for each address's last update

(define state->point #f) ;; map states to the graph nodes
(define (register-state s)
  (hash-ref! state->point s (λ _ (point s (seteq) #f (seteq) -1))))

;; terrible global to communicate to other functions
;; (parameters have the right semantics, but too slow in a hot loop)
(define current-point #f)

(define (join-actions oldA newA)
  (for/fold ([A oldA]) ([(addr age) (in-hash newA)])
    (hash-set A addr age)))

;; TODO: change state constructors to intern table lookup so that we can
;; represent the graph structure via sharing instead of indirection through
;; the E hash. Limits allocation and increases traversal speed.
(define (add-todo! p actions)
  (match-define (starting-point _ ps A) current-point)
  ;; add edge to graph
  (set-point-at-unions! p unions)
  (set-starting-point-points! current-point (∪1 ps p))
  (set-starting-point-actions! current-point (if A (join-actions A actions) actions)))
(trace add-todo!)

(define (add-todo/skip! p)
  (match-define (point state _ _ skips _) p)
  ;; XXX: Is this really all that's needed? Do we also need to
  ;; update the union count at each state on the path?
  (set-point-at-unions! p unions)
  (set-point-skips! current-point (∪1 skips p))
  (i:add-todo! state))
(trace add-todo/skip!)

(define (ensure-σ-size)
  (when (= next-loc (vector-length global-σ))
    (set-global-σ! (grow-vector global-σ next-loc))
    (set! σ-history (grow-vector σ-history next-loc))))

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
               (unless (= unions (point-at-unions p))
                 (add-todo! p actions)
                 (i:add-todo! state))
               actions)]))

(define (prepare-sparse-wide/prealloc parser sexp)
  (begin0 (prepare-prealloc parser sexp)
          (set! current-point (starting-point 'entry (seteq) ∅))
          (set! state->point (make-hash))
          (set! σ-history (make-vector (vector-length global-σ)))))
;; An address is consonant with a past state if its union count is smaller than
;; the union count of that state.
(define (actions-consonant? A)
  (and A
       (for/and ([(addr age) (in-hash A)])
         (= (vector-ref σ-history addr) age))))
(trace actions-consonant?)

;; Increase union count only if the abstract values have changed.
;; Also, save the union count for the modified address for future sparseness.
(define (join!/sparse a vs)
  (define prev (vector-ref global-σ a))
  (define upd (⊓ vs prev))
  (unless (≡ prev upd)
    (vector-set! global-σ a upd)
    (inc-unions!)
    (vector-set! σ-history a unions)))

(define (join*!/sparse as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join!/sparse a vs)))

;; FIXME: skipping logic
(define (skip-from ps)
  (define seen (make-hasheq))
  (let loop ([todo ps])
    (trace loop)
    (for ([p (in-set todo)]
          #:unless (hash-has-key? seen p))
      (hash-set! seen p #t)
      (match-define (point _ pp* A _ _) p)
      (cond [(actions-consonant? A)
             (printf "Consonant!~%")
             (loop pp*)]
            [else
             (printf "Skipped from ~a to ~a~%" todo p)
             (add-todo/skip! p)]))))
(trace skip-from)

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
      fst
      (define clean-σ (restrict-to-reachable/vector touches))
      (define sparse-step (mk-sparse-step step))
      (trace sparse-step)
      (let loop ()
        (cond [(∅? todo) ;; → null?
               (define vs
                 (for*/set ([(c _) (in-hash state->point)]
                            #:when (ans^? c))
                   (ans^-v c)))
               (cons global-σ state->point)
               #;
               (cons (clean-σ global-σ vs)
                     vs)]
              [else
               (define todo-old todo)
               (reset-todo!)
               (for ([c (in-set todo-old)])
                 (printf "Stepping ~a~%" c)
                 (sparse-step c))
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

(define-syntax-rule (with-sparse-mutable-worklist body)
  (splicing-syntax-parameterize
   ([yield-meaning yield-global-sparse])
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
