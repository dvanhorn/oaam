#lang racket
(require "primitives.rkt" "data.rkt" "notation.rkt"
         racket/stxparam racket/splicing
         (for-syntax syntax/parse syntax/parse/experimental/template
                     racket/syntax)
         "do.rkt" "context.rkt" "deltas.rkt" "handle-limits.rkt"
         "parameters.rkt" "add-lib.rkt"
         (for-template "primitives.rkt") racket/unsafe/ops
         (only-in "kcfa.rkt" parameters-minus analysis-parameters)
         "../../r-tree/pure-sparse-r-tree.rkt"
         "env.rkt" "parse.rkt"
         "nnmapc.rkt" "rtree-nnmapc.rkt" "spectral-heap.rkt" "simple-heap.rkt"
         syntax/parse/experimental/template
         racket/trace)
(provide with-sparse)

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
(define (new-sparse-graph) (make-hash)) ;; 1 lever hash Map[State,Node]
(define (new-graph) (make-hash)) ;; 2 level hash Map[State,Map[Heap,conf]]

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
(define (processed! conf)
  (unless (node-actions (conf-node conf))
    (error 'processed! "No actions, but processed ~a" conf))
  (set-conf-todo?! conf #f))

(define label 0) (define (reset-label!) (set! label 0))
(define (inc-label!) (begin0 label (set! label (add1 label))))
(define sparse-top-ctx '())
(define (sparse-ext-ctx label ctx kind) (cons label ctx))
(define (sparse-get-ctx ctx) (reverse ctx))
(define (sparse-fresh-label! ctx new?)
  (if new?
      (inc-label!)
      (cons (inc-label!) ctx)))
(define (sparse-fresh-variable! x ctx)
  (cons (gensym x) ctx))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-parameter target-actions (λ (stx) (raise-syntax-error #f "Actions unset" stx)))
(define-syntax-rule (initialize-actions body ...)
  (let ([initial-actions (hasheq)])
    (syntax-parameterize ([target-actions (make-rename-transformer #'initial-actions)])
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
    (unless (hash? actions) (error 'name "Bad ~a~%" actions))
    (for/set #:initial initial ([(a act) (in-hash actions)] #:when (pred act)) a)))
(mk-actions-collector actions-uses used?)
(mk-actions-collector actions-changes changed?)

(define (actions-consonant? ≅ actions)
  (unless (hash? actions) (error 'actions-consonant? "Bad ~a~%" actions))
  (for/and ([(a act) (in-hash actions)]
            #:when (used? act))
    (a . ∈ . ≅)))

(define-syntax-rule (bind-get-sparse (res σ a) body)
  (let ([aid a])
    #;(printf "Trying to get ~a, " aid)
  (let ([res (getter σ aid)]
        [actions (set-action target-actions aid U)])
    #;(printf "got ~a~%" res)
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body))))

(define-syntax-rule (safe-map-ref m k) (map-ref m k nothing))

(define-syntax-parameter sp-mk-fix #f)
(define-syntax-parameter sp-fix #f)
(define-syntax-parameter sp-ans #f)
(define-syntax-parameter sp-touches #f)
(define-syntax-rule (with-sparse (mk-analysis) . body)
  (begin
    (with-simple-heap
    (with-simple-nnmapc
    (define-syntax-rule (mk-conf state σ data)
      (conf state σ (node-of! sparse-graph state) (seteq) #t #;data))
    (define-syntax-rule (conf-of/data! g state σ data)
      (let ([hsh (begin
                   (unless (hash? g) (error 'BORF))
                   (hash-ref g state #f))])
        (cond
         [hsh (hash-ref! hsh σ (λ () (mk-conf state σ data)))]
         [else (define hsh (make-hash))
               (define c (mk-conf state σ data))
               (hash-set! hsh σ c)
               (hash-set! g state hsh)
               c])))
    (define-syntax-rule (register-conf/data/todo! g state σ data)
      (let ([hsh (begin
                   (unless (hash? g) (error 'BARF))
                   (hash-ref g state #f))])
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
    (define (conf-of g state σ)
      (and #:bind σ↦conf (hash-ref g state #f)
           (hash-ref σ↦conf σ #f)))
    
    (define (add-edge! from to-σ to actions)
      (define to-cnf (conf-of/todo! graph to to-σ))
      (match-define (conf _ _ from-node succ _ #;_data) from)
      (set-conf-succ! from (∪1 succ to-cnf))
      (set-node-actions! from-node (join-actions (node-actions from-node) actions))
      to-cnf)
    (define (add-sparse-edge! from to-σ to)
      (define fsm (node-succmap from))
      (set-node-succmap! from (map-map-add! fsm to-σ to)))

    (define-syntax-rule (bind-join-sparse (σ* σ a vs) body*)
      (let ([bind-actions (set-action target-actions a D)]
            [σ* (map-join-key σ a vs)])
        (syntax-parameterize ([target-actions (make-rename-transformer #'bind-actions)]
                              [target-σ (make-rename-transformer #'σ*)])
          body*)))

    ;; Fast-forward to state at a fast-forwarded store.
    (define (add-todo/skip! state last-σ start-conf σ actions)
      (define ffσ
        (for/fold ([σ σ]) ([(a act) (in-hash actions)]
                           #:when (changed? act))
          (map-join-key σ a (safe-map-ref last-σ a))))
      #;(printf "Skipping~%")
      (add-edge! start-conf ffσ state actions))
    ;; Find a skipping path through the sparse graph and collect the addresses that
    ;; get changed along the path.
    (define (skip-from ≅ cnfs σ actions)
      (define seen (make-hasheq))
      (let loop ( ;; successors of skipped state
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
            (unless (or actions-out todo?) (error 'todo/skip "Bad actions for ~a" cnf))
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
        (define (accept next-σ ≅ nds)
          (cond
           [next-σ
            (define actions (node-actions current-node))
            (define cnfs (for/fold ([acc (seteq)])
                             ([nd (in-map-map-values nds)])
                           #:break (not acc)
                           (and #:bind conf (conf-of graph (node-state nd) next-σ)
                                (∪1 acc conf))))            
            (if (and 
                 cnfs
                 (not (for/or ([cnf (in-set cnfs)])
                        (or (conf-todo? cnf)
                            (not (actions-consonant? ≅ actions))))))
                (values cnfs actions)
                (values #f #f))]
           [else (values #f #f)]))
        (printf "Rtree size ~a~%" (size succmap))
        (define-values (≅ cnfs actions) (map-map-close succmap σ accept))
        #;(printf "Start step~%")
        (cond [cnfs #;(printf "Skip ~a~%" (conf-state cnf))
                    (skip-from ≅ cnfs σ actions)]
              [else (step σ c)])
        #;(printf "End step~%")
        ;; FIXME: need invariant that node-actions is non-#f
        (processed! cnf)))

      (define-syntax (mk-sparse-fixpoint stx)
        (syntax-case stx ()
          [(_ name ans touches)
           (with-syntax ([(ans? ans-v)
                          (list (format-id #'ans "~a?" #'ans)
                                (format-id #'ans "~a-v" #'ans))])
             (syntax/loc stx
               (define-syntax-rule (name step fst)
                 (let ()
                   #;(printf "START~%")
                   (define clean-σ restrict-to-reachable)
                   (define state-count* (state-count))
                   (define last 0)
                   (mk-sparse-step sparse-step step)
                   (set-box! state-count* 0)
                   (set-box! (start-time) (current-milliseconds))
                   fst

                   (let loop ()
                     (cond
                      [(not (hash-iterate-first todo)) ;; empty set
                       (state-rate)
                       (define vs
                         (for*/set ([(c σ↦cnf) (in-hash graph)]
                                    #:when (ans? c)
                                    [(σ _) (in-hash
                                            (begin
                                              (unless (hash? σ↦cnf) (error 'fix "Bad ~a~%" σ↦cnf))
                                              σ↦cnf))])
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
                       (loop)]))))))]))

      
      ;; XXX: Per-state actions rather than per-transition actions make
      ;; narrowing given GC difficult/impossible. (Maybe not. Per-node use/def but per-state GC?)
      (define (do-narrow-yield σ actions state)
        #;(printf "Yielding~%")
        (define to-cnf (add-edge! current-conf σ state actions))
        (add-sparse-edge! (conf-node current-conf) σ (conf-node to-cnf)))
      #;(trace do-narrow-yield)

      (define-for-syntax (yield-narrow-sparse stx)
        (syntax-case stx ()
          [(_ e) #'(begin (do-narrow-yield target-σ target-actions e) (continue))]))

      ;; The final setup.
     (splicing-syntax-parameterize
         ([fresh-label! (make-rename-transformer #'sparse-fresh-label!)]
          [fresh-variable! (make-rename-transformer #'sparse-fresh-variable!)]
          [top-ctx (make-rename-transformer #'sparse-top-ctx)]
          [ext-ctx (make-rename-transformer #'sparse-ext-ctx)]
          [get-ctx (make-rename-transformer #'sparse-get-ctx)])
       (with-parse
        (with-add-lib
         (define (prepare-sparse parser sexp)
           (reset-label!)
           (define-values (e renaming ps) (parser sexp))
           (define e* (add-lib e renaming ps))
           (reset-graph!)
           (reset-sparse-graph!)
           (reset-todo!)
           (set-current-conf! (conf-of! graph 'initial (empty-heap)))
           e*)
         (splicing-syntax-parameterize
              ([bind-get (make-rename-transformer #'bind-get-sparse)]
               [cr-targets (list* σ-target actions-target (syntax-parameter-value #'cr-targets))]
               [getter (make-rename-transformer #'safe-map-ref)]
               [bind-join (make-rename-transformer #'bind-join-sparse)]
               [empty-heap (make-rename-transformer #'new-map)]
               [yield yield-narrow-sparse]
               [sp-mk-fix (make-rename-transformer #'mk-sparse-fixpoint)])
            (splicing-let-syntax
             ([new-tr
               (let ([in-tr (syntax-parameter-value #'in-scope-of-extras)])
                 (λ (stx)
                    (syntax-case stx ()
                      [(... (_ (extras ...) body* ...))
                       (in-tr (quasisyntax/loc stx
                                (...
                                 (in-scope-of-extras
                                  (extras ...)
                                  (sp-mk-fix #,(syntax-local-introduce
                                                (rename-transformer-target
                                                 (syntax-parameter-value #'sp-fix)))
                                             #,(syntax-local-introduce
                                                (rename-transformer-target
                                                 (syntax-parameter-value #'sp-ans)))
                                             #,(syntax-local-introduce
                                                (rename-transformer-target
                                                 (syntax-parameter-value #'sp-touches))))
                                  body* ...))))])))])
             (splicing-let-syntax
              ([mk-analysis
                (λ (stx)
                   (syntax-parse stx
                     [(_ p:analysis-parameters)
                      (quasitemplate/loc stx
                        (splicing-syntax-parameterize
                            ([in-scope-of-extras (syntax-local-value #'new-tr)]
                             [sp-fix (make-rename-transformer #'fixpoint)]
                             [sp-ans (make-rename-transformer #'p.ans)]
                             [sp-touches (make-rename-transformer #'p.touches-id)])
                          (mk-analysis #:ans p.ans
                                       #:fixpoint sp-fix
                                       #:touches p.touches-id
                                       #:prepare (?? p.prep-fn
                                                     (λ (sexp) (prepare-sparse parse-prog sexp)))
                                       #,@(parameters-minus #'(p.all (... ...))
                                                            '(#:fixpoint #:ans #:touches #:prepare)))))]))])
              . body))))))))))
