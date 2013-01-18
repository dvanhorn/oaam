#lang racket
(require "primitives.rkt" "data.rkt" "notation.rkt" racket/stxparam racket/splicing
         "do.rkt" "context.rkt" "deltas.rkt" "handle-limits.rkt"
         "parameters.rkt" "nnmapc.rkt" "add-lib.rkt"
         (for-template "primitives.rkt") racket/unsafe/ops
         "env.rkt" "parse.rkt"
         racket/trace)
(provide prepare-sparse mk-sparse-fixpoint with-sparse)

(define (list-index lst elm)
  (let loop ([lst lst] [i 0])
    (match lst
      [(cons a lst) (if (equal? elm a) i (loop lst (add1 i)))]
      [else #f])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sparse analyses accumulate actions on uses and changes of addresses.

;; Sparse graph nodes differ from graph nodes in that they have an extra level
;; of indirection. Successors are partitioned by heap, so succ is now "succmap"
;; for mapping heaps to sets of snodes.
;; Data is also flattened to have the necessary fields represented in the node:
;;  actions/todo?/skips
(struct node (state [succmap #:mutable] [actions #:mutable]) #:prefab)
(struct conf (state σ
              [node #:mutable] ;; point to the node classifying all contexts of state
              [succ #:mutable]
              [todo? #:mutable]
              #;[data #:mutable]) #:prefab)

(define-syntax-rule (mk-node state)
  (node state (new-map-map) #f))
(define-syntax-rule (mk-conf state σ data)
  (conf state σ (node-of! sparse-graph state) (seteq) #t #;data))
(define (new-sparse-graph) (make-hash)) ;; 1 lever hash Map[State,Node]
(define (new-graph) (make-hash)) ;; 2 level hash Map[State,Map[Heap,conf]]
(define-syntax-rule (conf-of/data! g state σ data)
  (let ([hsh (hash-ref g state #f)])
    (cond
     [hsh (hash-ref! hsh σ (λ () (mk-conf state σ data)))]
     [else (define hsh (make-hash))
           (define c (mk-conf state σ data))
           (hash-set! hsh σ c)
           (hash-set! g state hsh)
           c])))
(define-syntax-rule (register-conf/data/todo! g state σ data)
  (let ([hsh (hash-ref g state #f)])
    (cond
     [hsh (hash-ref! hsh σ
                     (λ ()
                        (define c (mk-conf state σ data))
                        (hash-set! hsh σ c)
                        (hash-set! todo c #t)
                        c))]
     [else (define hsh (make-hash))
           (define c (mk-conf state σ data))
           (hash-set! hsh σ c)
           (hash-set! g state hsh)
           (hash-set! todo c #t)
           c])))
(define (node-of! g state) (hash-ref! g state (λ () (mk-node state))))
(define (conf-of! g state σ) (conf-of/data! g state σ #f))
(define (conf-of/todo! g state σ) (register-conf/data/todo! g state σ #f))
(define (conf-of g state σ) (hash-ref (hash-ref g state) σ))

(define (add-sparse-edge! from to-σ to)
  (define fsm (node-succmap from))
  (set-node-succmap! from (map-map-set fsm to-σ
                                       (∪1 (map-map-ref fsm to-σ (seteq)) to))))
(define (add-edge! from to-σ to actions)
  (define to-cnf (conf-of/todo! graph to to-σ))
  (match-define (conf _ _ from-node succ _ #;_data) from)
  (set-conf-succ! from (∪1 succ to-cnf))
  (set-node-actions! from-node (join-actions (node-actions from-node) actions))
  to-cnf)

;; Fast-forward to state at a fast-forwarded store.
(define (add-todo/skip! state last-σ start-conf σ actions)
  (define ffσ
    (for/fold ([σ σ]) ([(a act) (in-hash actions)]
                       #:when (changed? act))
      (map-join σ a (map-ref last-σ a))))
  (add-edge! start-conf ffσ state actions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Globals
(define graph #f) ;; Points are stored near all different
(define sparse-graph #f)
(define todo #f)
(define current-conf #f) (define (set-current-conf! conf) (set! current-conf conf))
(define (reset-graph!) (set! graph (new-graph)))
(define (reset-sparse-graph!) (set! sparse-graph (new-graph)))
(define (reset-todo!) (set! todo (make-hasheq)))

;; Should already be seen, so the ref won't fail.
(define (processed! conf) (set-conf-todo?! conf #f))
(define (prepare-sparse parser sexp)
  (define label 0) (define (inc-label!) (begin0 label (set! label (add1 label))))
  (define (sparse-fresh-label! ctx new?)
    (if new?
        (inc-label!)
        (cons ctx (inc-label!))))
  (define (sparse-fresh-variable! x ctx)
    (cons ctx (gensym x)))
  (define-values (e renaming ps) (parser sexp sparse-fresh-label! sparse-fresh-variable!))
  (define e* (add-lib e renaming ps sparse-fresh-label! sparse-fresh-variable!))
  e*)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-parameter target-actions (λ (stx) (raise-syntax-error #f "Actions unset" stx)))
(define-syntax-rule (initialize-actions body ...)
  (let ([actions (hasheq)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body ...)))
(define-for-syntax actions-target
  (target #'target-actions '#:actions (make-rename-transformer #'initialize-actions)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lattice of actions
;;   U/D         3
;; U     D    2     1
;;   N/A         0
(define (⊓-action a₀ a₁) (bitwise-ior a₀ a₁))
(define U/D 3)
(define U 2)
(define D 1)
(define N/A 0)
(define (used? a) (not (zero? (bitwise-and a 2))))
(define (changed? a) (not (zero? (bitwise-and a 1))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (set-action As addr kind)
  (hash-set As addr (⊓-action kind (hash-ref As addr N/A))))

(define (join-actions oldA newA)
  (cond [(eq? oldA newA) oldA]
        [oldA (for/fold ([A oldA]) ([(addr kind) (in-hash newA)])
                (set-action A addr kind))]
        [else newA]))

(define-syntax-rule (mk-actions-collector name pred)
  (define (name actions [initial ∅])
    (for/set #:initial initial ([(a act) (in-hash actions)] #:when (pred act)) a)))
(mk-actions-collector actions-uses used?)
(mk-actions-collector actions-changes changed?)

(define (actions-consonant? ≅ actions)
  (for/and ([(a act) (in-hash actions)]
            #:when (used? act))
    (a . ∈ . ≅)))

;; Find a skipping path through the sparse graph and collect the addresses that
;; get changed along the path.
(define (skip-from ≅ cnfs σ actions)
  (define seen (make-hasheq))
  (let loop (;; successors of skipped state
             [from-cnfs cnfs]
             ;; Accumulated heap changes along path
             [actions actions])
    (for ([cnf (in-set from-cnfs)])
      (cond
       [(hash-has-key? seen cnf) (void)]
       [else
        (hash-set! seen cnf #t)
        (match-define (conf state last-σ node succ todo? #;_data) cnf)
        (define actions-out (node-actions node))
        (if (or ;; Can't skip a state yet be stepped.
                todo?
                ;; Can't travel across an edge that uses addresses
                ;; not consonant with the current heap.
                (not (actions-consonant? ≅ actions-out)))
            (add-todo/skip! state last-σ current-conf σ actions)
            (loop succ (join-actions actions-out actions)))]))))

(define-simple-macro* (mk-sparse-step name step)
  (define (name cnf) ;; expects #:wide to be used to separate σ from state.
    (match-define (conf c σ current-node succ todo? #;data) cnf)
    (set-current-conf! cnf)
    (define succmap (node-succmap current-node))
    (define-values (next-σ ≅) (map-map-close succmap σ))
    (cond [next-σ
           (define nds (map-map-ref succmap next-σ))
           (cond [nds
                  (define actions (node-actions current-node))
                  #;(printf "Succ~%")
                  (define cnfs (for/seteq ([nd (in-set nds)])
                                 (conf-of graph (node-state nd) next-σ)))
                  (cond
                   [(not (for/or ([cnf (in-set cnfs)])
                           (or (conf-todo? cnf)
                               (not (actions-consonant? ≅ actions)))))
                    #;
                    (printf "Skip ~a~%" (conf-state cnf))
                    (skip-from ≅ cnfs σ actions)]
                   [else (step σ c)])]
                 [else (step σ c)])]
          [else (step σ c)])
    (processed! cnf)))

(define-syntax-rule (mk-sparse-fixpoint name ans? ans-v touches)
  (define-syntax-rule (name step fst)
     (let ()
      (define clean-σ (restrict-to-reachable touches))
      (define state-count* (state-count))
      (define last 0)
      (mk-sparse-step sparse-step step)
      (set-box! state-count* 0)
      (reset-graph!)
      (reset-sparse-graph!)
      (reset-todo!)
      (set-current-conf! (conf-of! graph 'initial (empty-heap)))
      (set-box! (start-time) (current-milliseconds))
      fst

      (let loop ()
        (cond
         [(not (hash-iterate-first todo)) ;; empty set
          (state-rate)
          (define vs
            (for*/set ([(c σ↦cnf) (in-hash graph)]
                       #:when (ans? c)
                       [(σ _) (in-hash σ↦cnf)])
              (list (clean-σ σ (ans-v c))
                    (ans-v c))))
          (values (format "State count: ~a" (unbox state-count*))
                  vs)]

         [else
          (define todo-old todo)
          (set-box! state-count* (+ (unbox state-count*)
                                    (hash-count todo-old)))
          (when (> (- (unbox state-count*) last) 1000)
            (set! last (unbox state-count*))
            (printf "States: ~a~%" last))
          (reset-todo!)
          (for ([(conf _) (in-hash todo-old)]) (sparse-step conf))
          (loop)])))))

;; XXX: Per-state actions rather than per-transition actions make
;; narrowing given GC difficult/impossible.
(define (do-narrow-yield σ actions state)
  (define to-cnf (add-edge! current-conf σ state actions))
  (add-sparse-edge! (conf-node current-conf) σ (conf-node to-cnf)))

(define-for-syntax (yield-narrow-sparse stx)
  (syntax-case stx ()
    [(_ e) #'(begin (do-narrow-yield target-σ target-actions e) (continue))]))

(define-syntax-rule (bind-get-sparse (res σ a) body)
  (let ([res (getter σ a)]
        [actions (set-action target-actions a U)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body)))

(define (map-join m k vs)
  (map-set m k (⊓ (map-ref m k) vs)))

(define-syntax-rule (bind-join-sparse (σ* σ a vs) body)
  (let ([actions (set-action target-actions a D)]
        [σ* (map-join σ a vs)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)]
                          [target-σ (make-rename-transformer #'σ*)])
      body)))

(define-syntax-rule (with-sparse body)
  (splicing-syntax-parameterize
   ([bind-get (make-rename-transformer #'bind-get-sparse)]
    [cr-targets (list* σ-target actions-target (syntax-parameter-value #'cr-targets))]
    [getter (make-rename-transformer #'map-ref)]
    [bind-join (make-rename-transformer #'bind-join-sparse)]
    [empty-heap (make-rename-transformer #'new-map)]
    [yield yield-narrow-sparse])
   body))
