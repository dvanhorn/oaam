#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         (only-in "store-passing.rkt" bind-help) "data.rkt" "deltas.rkt" "add-lib.rkt"
         "handle-limits.rkt" "graph.rkt")
(provide reset-globals! reset-todo! add-todo! inc-unions! set-global-σ!
         saw-change!
         reset-saw-change?!
         mk-mk-imperative/timestamp^-fixpoint
         mk-mk-imperative/∆s/acc^-fixpoint
         mk-mk-imperative/∆s^-fixpoint
         mk-imperative/timestamp^-fixpoint
         mk-imperative/∆s/acc^-fixpoint
         mk-imperative/∆s^-fixpoint
         mk-add-∆/s
         mk-add-∆/s!
         prepare-imperative
         unions todo seen global-σ graph reset-graph!
         current-state set-current-state!
         with-mutable-store
         with-mutable-worklist
         with-σ-∆s/acc!
         with-σ-∆s!)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable global store and worklist.
(define todo #f)
(define seen #f)
(define global-σ #f)
(define current-state #f) ;; for graphs
(define graph #f)
(define (set-current-state! v) (set! current-state v))
(define (reset-graph!) (set! graph (new-graph)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(define unions #f)
(define (inc-unions!) (set! unions (add1 unions)))

(define (do-yield c)
  (unless (= unions (hash-ref seen c -1))
    (hash-set! seen c unions)
    (add-todo! c)))
(define (do-yield-graph c)
  (unless (= unions (hash-ref seen c -1))
    (hash-set! seen c unions)
    (add-todo! c)
    (add-edge! graph current-state c)))

(define-for-syntax (yield! stx)
  (syntax-case stx ()
    [(_ e)
     #`(begin #,(if (syntax-parameter-value #'generate-graph?)
                    #`(do-yield-graph e)
                    #`(do-yield e))
              (continue))])) ;; ∪1 → cons

(define (join-h! a vs)
  (define prev (hash-ref global-σ a ∅))
  (define upd (⊓ vs prev))
  (unless (≡ prev upd)
    (hash-set! global-σ a upd)
    (inc-unions!)))
(define-syntax-rule (bind-join-h! (σ* jhσ a vs) body)
  (begin (join-h! a vs) body))

(define (join*-h! as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join-h! a vs)))
(define-syntax-rule (bind-join*-h! (σ* jh*σ as vss) body)
  (begin (join*-h! as vss) body))

(define-simple-macro* (mk-mk-imperative/timestamp^-fixpoint mk-name cleaner)
  (define-syntax-rule (mk-name name ans^? ans^-v touches)
    (define-syntax-rule (name step fst)
      (let ()
        (set-box! (start-time) (current-milliseconds))
        fst
        (define state-count* (state-count))
        (define last 0)
        (set-box! state-count* 0)
        (define clean-σ (cleaner touches))
        (let loop ()
          (cond [(∅? todo) ;; → null?
                 (state-rate)
                 (define vs
                   (for*/set ([(c at-unions) (in-hash seen)]
                              #:when (ans^? c))
                     (ans^-v c)))
               (pretty-print
                (for/list ([v (in-vector global-σ)]
                           [i (in-naturals)])
                  (cons i v)))
                 (values (format "State count: ~a" (unbox state-count*))
                         (format "Point count: ~a" (hash-count seen))
                         #;
                         global-σ
                         
                         (clean-σ global-σ vs)
                         vs)]
                [else
                 (define todo-old todo)
                 (reset-todo!) ;; → '()
                 (define count (+ (unbox state-count*) (set-count todo-old)))
                 (set-box! state-count* count)
                 (when (>= (- count last) 1000)
                   (printf "States: ~a~%" count)
                   (set! last count))
                 (for ([c (in-set todo-old)])
                   #,@(when-graph #'(set-current-state! c))
                   (step c)) ;; → in-list
                 (loop)]))))))
(mk-mk-imperative/timestamp^-fixpoint
 mk-imperative/timestamp^-fixpoint restrict-to-reachable)

(define-syntax-rule (with-mutable-worklist body)
  (splicing-syntax-parameterize
   ([yield yield!])
   body))
(define-syntax-rule (with-mutable-store body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-h!)]
    [bind-join* (make-rename-transformer #'bind-join*-h!)]
    [getter (make-rename-transformer #'global-hash-getter)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accumulated deltas
(define (do-yield/∆s/acc! c)
  (when (or saw-change?
            (not (= unions (hash-ref seen c -1))))
    (hash-set! seen c unions)
    (add-todo! c)))

(define (do-yield/∆s/acc!-graph c)
  (when (or saw-change?
            (not (= unions (hash-ref seen c -1))))
    (hash-set! seen c unions)
    (add-edge! graph current-state c)
    (add-todo! c)))

(define-for-syntax (yield/∆s/acc! stx)
  (syntax-case stx ()
    [(_ e) (if (syntax-parameter-value #'generate-graph?)
               #`(begin (do-yield/∆s/acc!-graph e)
                        (continue))
               #`(begin (do-yield/∆s/acc! e)
                        (continue)))]))

(define-syntax-rule (mk-add-∆/s add-∆ add-∆s bind-join bind-join* get-σ)
  (begin
    (define (add-∆ acc a vs)
      (define prev (get-σ global-σ a nothing))
      (define next (⊓ prev vs))
      (cond [(≡ prev next) acc]
            [else (saw-change!)
                  (cons (cons a vs) acc)]))
    (define (add-∆s acc as vss)
      (let loop ([as as] [vss vss])
        (match* (as vss)
          [((cons a as) (cons vs vss))
           (add-∆ (loop as vss) a vs)]
          [('() '()) acc]
          [(_ _)
           (error 'add-∆s "Expected same length lists. Finished at ~a ~a"
                  as vss)])))
    (define-simple-macro* (bind-join* (∆s* ∆s as vss) body)
      (let ([∆s* (add-∆s ∆s as vss)]) #,(bind-help #'∆s* #'body)))
    (define-simple-macro* (bind-join (∆s* ∆s a vs) body)
      (let ([∆s* (add-∆ ∆s a vs)]) #,(bind-help #'∆s* #'body)))))
(mk-add-∆/s add-∆ add-∆s bind-join-∆s/change bind-join*-∆s/change hash-ref)

(define-syntax-rule (with-σ-∆s/acc! body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-∆s/change)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s/change)]
    [yield yield/∆s/acc!]
    [getter (make-rename-transformer #'global-hash-getter)])
            body))

(define-syntax-rule (mk-mk-imperative/∆s/acc^-fixpoint mk-name cleaner joiner set-σ! get-σ)
  (define-syntax-rule (mk-name name ans^? ans^-v touches)
    (define-syntax-rule (name step fst)
      (let ()
      (set-box! (start-time) (current-milliseconds))
      ;; fst contains all the ∆s from the first step(s)
      (for ([a×vs (in-list fst)]) (joiner (car a×vs) (cdr a×vs)))
      (inc-unions!)
      (define state-count* (state-count))
      (set-box! state-count* 0)
      (define clean-σ (cleaner touches))
      (let loop ()
        (cond [(∅? todo)
               (state-rate)
               (define vs
                 (for*/set ([(c at-unions) (in-hash seen)]
                            #:when (ans^? c))
                   (ans^-v c)))
               (values (format "State count: ~a" (unbox state-count*))
                       (format "Point count: ~a" (hash-count seen))
                       (clean-σ global-σ vs)
                       vs)]
              [else
               (define todo-old todo)
               (reset-todo!)
               (set-box! state-count* (+ (unbox state-count*) (set-count todo-old)))
               (define ∆s (for/append ([c (in-set todo-old)])
                            (reset-saw-change?!)
                            (step c)))
               (for* ([a×vs (in-list ∆s)])
                 (define a (car a×vs))
                 (set-σ! global-σ a (⊓ (get-σ global-σ a nothing) (cdr a×vs))))
               ;; Only one inc needed since all updates are synced.
               (unless (null? ∆s) (inc-unions!))
               (loop)]))))))
(mk-mk-imperative/∆s/acc^-fixpoint
 mk-imperative/∆s/acc^-fixpoint restrict-to-reachable join-h! hash-set! hash-ref)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Imperative deltas
(define global-∆s #f)
(define (set-global-∆s! v) (set! global-∆s v))
(define saw-change? #f) ;; nasty global to communicate that a state is new
(define (reset-saw-change?!) (set! saw-change? #f))
(define (saw-change!) (set! saw-change? #t))
(define-syntax-rule (mk-add-∆/s! add-∆! add-∆s! bind-join bind-join* get-σ)
  (begin
    (define (add-∆! a vs)
      (define prev (get-σ global-σ a nothing))
      (define next (⊓ prev vs))
      (unless (≡ prev next)
        (saw-change!) ;; add-todo should actually add.
        (set-global-∆s! (cons (cons a vs) global-∆s))))
    (define (add-∆s! as vss)
      (set-global-∆s! (for/fold ([acc global-∆s])
                          ([a (in-list as)]
                           [vs (in-list vss)]
                           #:unless (let* ([prev (get-σ global-σ a nothing)]
                                           [next (⊓ prev vs)])
                                      (or (≡ next prev)
                                          (not (saw-change!)))))
                        (cons (cons a vs) acc))))
    (define-simple-macro* (bind-join (∆s* ∆s a vs) body)
      (begin (add-∆! a vs) body))
    (define-simple-macro* (bind-join* (∆s* ∆s as vss) body)
      (begin (add-∆s! as vss) body))))
(mk-add-∆/s! add-∆! add-∆s! bind-join-∆s! bind-join*-∆s! hash-ref)

(define (yield/∆s! c)
  (when (or saw-change?
            (not (= unions (hash-ref seen c -1))))
    (hash-set! seen c unions)
    (add-todo! c)))

(define (yield/∆s!-graph c)
  (when (or saw-change?
            (not (= unions (hash-ref seen c -1))))
    (hash-set! seen c unions)
    (add-edge! graph current-state c)
    (add-todo! c)))

(define-for-syntax (yield/∆s! stx)
  (syntax-case stx ()
    [(_ e) #`(begin #,(if (syntax-parameter-value #'generate-graph?)
                          #'(yield/∆s!-graph e)
                          #'(yield/∆s! e))
                    (continue))]))

(define-syntax-rule (with-σ-∆s! body)
  (splicing-syntax-parameterize
   ([yield yield/∆s!]
    [bind-join (make-rename-transformer #'bind-join-∆s!)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s!)]
    [getter (make-rename-transformer #'global-hash-getter)])
   body))

(define-simple-macro* (mk-mk-imperative/∆s^-fixpoint mk-name cleaner joiner set-σ! get-σ)
  (define-syntax-rule (mk-name name ans^? ans^-v touches)
    (define-syntax-rule (name step fst)
       (let ()
      ;; fst contains all the ∆s from the first step(s)
      (set-box! (start-time) (current-milliseconds))
      fst
      (for ([a×vs (in-list global-∆s)]) (joiner (car a×vs) (cdr a×vs)))
      (reset-∆s!)
      (define state-count* (state-count))
      (set-box! state-count* 0)
      (define clean-σ (cleaner touches))
      (let loop ()
        (cond [(∅? todo)
               (state-rate)
               (define vs
                 (for*/set ([(c at-unions) (in-hash seen)]
                            #:when (ans^? c))
                   (ans^-v c)))
               (values (format "State count: ~a" (unbox state-count*))
                       (format "Point count: ~a" (hash-count seen))
                       (clean-σ global-σ vs)
                       vs)]
              [else
               (define todo-old todo)
               (reset-todo!)
               (set-box! state-count* (+ (unbox state-count*) (set-count todo-old)))
               ;; REMARK: there are a couple ways that we can populate the "seen"
               ;; hash.
               ;; 1) determine at every yield if the store changes
               ;;    actually grow the store, and populate accordingly.
               ;; 2) Associate changes with "todo" and after a step has occurred
               ;;    and we're updating the store, we change "seen" AND "todo" accordingly.
               ;; 3) Keep a secondary global store that is changed on each yield
               ;;    and which governs changing "seen." After the step, bang in the
               ;;    secondary store. (Requires an /immutable/ global store to avoid large copies)
               ;; We choose the first option since it's the cheapest.
               (for ([c (in-set todo-old)])
                 (reset-saw-change?!)
                 #,@(when-graph #'(set-current-state! c))
                 (step c))
               ;; Integrate all the store diffs accumulated over the last
               ;; frontier steps.
               ;; We know that changes MUST change the store by the add-∆s functions
               (for* ([a×vs (in-list global-∆s)])
                 (define a (car a×vs))
                 (set-σ! global-σ a (⊓ (get-σ global-σ a nothing) (cdr a×vs))))
               ;; Only one inc needed since all updates are synced.
               (unless (null? global-∆s) (inc-unions!))
               (reset-∆s!)
               (loop)]))))))
(mk-mk-imperative/∆s^-fixpoint
  mk-imperative/∆s^-fixpoint restrict-to-reachable join-h! hash-set! hash-ref)

(define (reset-∆s!) (set! global-∆s '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common functionality
(define (reset-globals! σ)
  (set! unions 0)
  (reset-graph!)
  (set! current-state (node 'entry (seteq) #f))
  (set! saw-change? #f)
  (set! todo ∅)
  (set! seen (make-hash))
  (set! global-σ σ)
  (set! global-∆s '()))
(define (set-global-σ! v) (set! global-σ v))
(define (reset-todo!) (set! todo ∅))
(define (add-todo! c) (set! todo (∪1 todo c)))

(define (prepare-imperative parser sexp)
  (define-values (e renaming ps) (parser sexp gensym gensym))
  (define e* (add-lib e renaming ps gensym gensym))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (reset-globals! (make-hash))
  e*)

(define-syntax-rule (global-hash-getter σ* a)
  (hash-ref global-σ a (λ () (error 'global-hash-getter "Unbound address ~a" a))))
