#lang racket
(require "primitives.rkt" "data.rkt" "notation.rkt" racket/stxparam racket/splicing
         "do.rkt" "context.rkt" "deltas.rkt" "prealloc.rkt" "handle-limits.rkt"
         "env.rkt" (rename-in "imperative.rkt" [add-todo! i:add-todo!]))
(provide mk-sparse^-fixpoint with-sparse^
         with-sparse-mutable-worklist
         with-0-ctx/prealloc/sparse
         prepare-sparse-wide/prealloc)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instrumented fixpoint for /widened/ step function xthat takes
;;; "big steps" when it can find reusable paths through the abstract state graph.

;; The wide story is less nuanced than the narrow one. In particular,
;; - ill-formed states are impossible
;; - "change" actions are unnecessary to track (all changes made to same store)
;; - congruence is equality of address ages. (last modified, and age when last used at a state)

;; - actions start at #f to distinguish "none" from "unknown"
;; - todo? blocks skipping past a point. We cannot soundly skip a state
;;   until it has been processed, since extra edges might be added that skipping
;;   would have to traverse to stay sound. After a state has been stepped and is not
;;   part of the todo set afterwards, todo? is reset to #f
(struct point (state points actions todo? skips) #:mutable #:prefab)
;; Stores the union count for each address's last update
(define σ-history #f)
;; Any store changes during this step?
(define ∆? #f)
;; States intern to mutable "points" that represent the annotated state graph
(define state->point #f)
;; Intern states.
(define (register-state s)
  (hash-ref! state->point s (λ _ (point s (seteq) #f #t (seteq)))))

;; terrible global to communicate to other functions
;; (parameters have the right semantics, but too slow in a hot loop)
(define current-point #f)

(define (join-actions oldA newA)
  (for/fold ([A oldA]) ([(addr age) (in-hash newA)])
    (hash-set A addr (max age (hash-ref oldA addr 0)))))
(define (join-actions/change oldA newA)
  (for/fold ([A oldA] [change? #f]) ([(addr age) (in-hash newA)])
    (define old-age (hash-ref oldA addr -1))
    (if (> age old-age)
        (values (hash-set A addr age) #t)
        (values A change?))))

;; Add p to current-point's outgoing edges and return if the given actions
;; changed value since last time, or if the point added is new.
(define (add-todo p actions)
  (define current-A (point-actions current-point))
  (define ps (point-points current-point))
  (define ps* (∪1 ps p))
  (set-point-points! current-point ps*)
  (define-values (A* change?)
    (if current-A
        (join-actions/change current-A actions)
        (values actions #t)))
  (set-point-actions! current-point A*)
  (or change? (> (set-count ps*) (set-count ps))))

(define (add-todo/skip! p)
  (set-point-skips! current-point (∪1 (point-skips current-point) p))
  (set-point-todo?! p #t)
  (i:add-todo! (point-state p)))

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
               ;; If stepping changed the store, or if the addresses this point
               ;; depends on changed since last interpretation, it must be
               ;; re-processed.
               (define change? (add-todo p actions))
               (cond [(or change? ∆?)
                      (set-point-todo?! p #t)
                      (i:add-todo! state)]
                     [else (void)])
               actions)]))

(define (skip-from ps)
  (define seen (make-hasheq)) ;; no intermediate allocation. eq? okay
  (let loop ([todo ps])
    (for ([p (in-set todo)]
          #:unless (and (hash-has-key? seen p)
                        #;
                        (printf "Seen (skip) ~a~%" (point-state p))))
      (hash-set! seen p #t)
      (match-define (point state-debug pp* A todo? _) p)
      (cond [(and (not todo?) (actions-consonant? A))
             (loop pp*)]
            [else (add-todo/skip! p)]))))

(define (prepare-sparse-wide/prealloc parser sexp)
  (begin0 (prepare-prealloc parser sexp)
          (set! current-point (point 'entry (seteq) #f #t (seteq)))
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
         (set! ∆? #t)
         (inc-unions!)
         (vector-set! σ-history a unions)]))

(define (join*!/sparse as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join!/sparse a vs)))

(define ((mk-sparse-step step) c)
  (set! current-point (register-state c))
  (set! ∆? #f)
  (match-define (point _ ps A _ _) current-point)
  (set-point-todo?! current-point #f)
  (if (actions-consonant? A)
      (skip-from ps)
      (step c)))

(define-syntax-rule (mk-sparse^-fixpoint name ans^? ans^-v touches)
  (define-syntax-rule (name step fst)
    (let ()
      (set-box! (start-time) (current-milliseconds))
      (define state-count* (state-count))
      (set-box! state-count* 0)
      fst
      (define clean-σ (restrict-to-reachable/vector touches))
      (define sparse-step (mk-sparse-step step))
      (let loop ()
        (cond
         [(∅? todo)
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
          (reset-todo!)
          (set-box! state-count* (+ (unbox state-count*)
                                    (set-count todo-old)))
          (for ([c (in-set todo-old)]) (sparse-step c))
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
