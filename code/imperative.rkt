#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         (only-in "store-passing.rkt" bind-rest) "data.rkt" "deltas.rkt" "add-lib.rkt"
         "handle-limits.rkt"
         racket/unsafe/ops)
(provide reset-globals! reset-todo! add-todo! inc-unions! set-global-σ!
         saw-change!
         reset-saw-change?!
         mk-mk-imperative/timestamp^-fixpoint
         mk-mk-imperative/∆s/acc^-fixpoint
         mk-mk-imperative/∆s^-fixpoint
         mk-imperative/timestamp^-fixpoint
         mk-imperative/timestamp^-fixpoint/stacked
         mk-imperative/∆s/acc^-fixpoint
         mk-imperative/∆s^-fixpoint
         mk-add-∆/s
         mk-add-∆/s!
         mk-join* mk-joiner mk-joiner/stacked mk-bind-joiner mk-global-store-getter mk-with-store mk-global-store-getter/stacked
         reset-∆?! ∆?
         prepare-imperative
         unions todo seen global-σ get-unions get-unions/Δ
         with-mutable-store
         with-mutable-store/stacked
         with-mutable-worklist
         with-mutable-worklist/stacked
         with-σ-∆s/acc!
         with-σ-∆s!)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable global store and worklist.
(define todo #f) (define todo-num 0)
(define seen #f)
(define global-σ #f)
(define ∆? #f)
(define (set-∆?!) (set! ∆? #t))
(define (reset-∆?!) (when ∆? (inc-unions!) (set! ∆? #f)))

(define empty-todo '())
(define empty-todo? null?)
(define (add-todo! c)
  (set! todo (cons c todo))
  (set! todo-num (add1 todo-num)))
(define-syntax in-todo (make-rename-transformer #'in-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(define unions #f)
(define (inc-unions!) (set! unions (add1 unions)))

(define (do-yield! c)
  (unless (= unions (hash-ref seen c -1))
    (hash-set! seen c unions)
    (add-todo! c)))
(define (do-yield/stacked! c)
  (define stack (hash-ref seen c '()))
  ;; We have seen this state before if there has been no store change and
  ;; the current timestamp is at the top of the stack.
  (define top-op (and (pair? stack) (car stack)))
  (define (do-add1)
    (hash-set! seen c (cons (add1 unions) stack))
    (add-todo! c))
  (define (do-add)
    (hash-set! seen c (cons unions stack))
    (add-todo! c))
  (if ∆?
       (if top-op
           ;; Saw state previously, but there was a store update. 
           (if (>= unions top-op)
               (do-add1)
               (void))
           ;; haven't seen state before, and there was a store update.
           (do-add1))
       (if top-op
           ;; saw the state at a previous store
           (if (> unions top-op)
               (do-add)
               (void))
           ;; haven't seen state before
           (do-add))))

(define-for-syntax yield! (syntax-rules () [(_ e) (do-yield! e)]))
(define-for-syntax yield/stacked! (syntax-rules () [(_ e) (do-yield/stacked! e)]))

(define-syntax-rule (mk-bind-joiner name joiner)
  (define-syntax-rule (name (σ* jhσ a vs) body)
    (begin (joiner a vs) body)))
(define-syntax-rule (mk-joiner name getter setter)
  (define (name a vs)
    (define prev (getter global-σ a ∅))
    (define upd (⊓ vs prev))
    (unless (≡ prev upd)
      (setter global-σ a upd)
      (inc-unions!))))
(define-syntax-rule (mk-join* name joiner)
  (define (name as vss)
    (for ([a (in-list as)]
          [vs (in-list vss)])
      (joiner a vs))))

(define-syntax-rule (mk-joiner/stacked name getter setter)
  (define (name a vs)
    (define (add t vs stack)
      (set-∆?!)
      (setter global-σ a (cons (cons t vs) stack)))
    (match (getter global-σ a '())
      ['() (add (add1 unions) vs '())]
      [(and stack (cons (cons t vs*) stack*))
       (define upd (⊓ vs vs*))
       (unless (≡ upd vs*)
         (if (< t unions)
             (add (add1 unions) upd stack)
             (add t upd stack*)))]
      [sv (error 'name "Bad store value at ~a: ~a" a sv)])))
(mk-joiner join-h! hash-ref hash-set!)
(mk-joiner/stacked join-h/stacked! hash-ref hash-set!)
(mk-bind-joiner bind-join-h! join-h!)
(mk-bind-joiner bind-join-h/stacked! join-h/stacked!)

(mk-join* join*-h! join-h!)
(mk-join* join*-h/stacked! join-h/stacked!)
(mk-bind-joiner bind-join*-h! join*-h!)
(mk-bind-joiner bind-join*-h/stacked! join*-h/stacked!)

(define-syntax-rule (mk-mk-imperative/timestamp^-fixpoint mk-name cleaner extra-reset extra-out ...)
  (define-syntax-rule (mk-name name ans^? ans^-v touches)
    (define-syntax-rule (name step fst)
      (let ()
        (set-box! (start-time) (current-milliseconds))
        fst
        (define state-count* (state-count))
        (set-box! state-count* 0)
        (define clean-σ (cleaner touches))
        (let loop ()
          (cond [(empty-todo? todo) ;; → null?
                 (state-rate)
                 (define vs
                   (for*/set ([(c at-unions) (in-hash seen)]
                              #:when (ans^? c))
                     (ans^-v c)))
                 (values (format "State count: ~a" (unbox state-count*))
                         (format "Point count: ~a" (hash-count seen))
                         
                         global-σ
                         ;;(clean-σ global-σ vs)
                         vs
                         extra-out ...)]
                [else
                 (define todo-old todo)
                 extra-reset
                 (set-box! state-count* (+ (unbox state-count*) todo-num))
                 (reset-todo!) ;; → '()
                 (for ([c (in-todo todo-old)])
                   (step c)) ;; → in-list
                 (loop)]))))))
(mk-mk-imperative/timestamp^-fixpoint
 mk-imperative/timestamp^-fixpoint restrict-to-reachable (void))

(define (restrict-to-reachable/stacked touches)
  (define rtr (restrict-to-reachable touches))
  (λ (σ v)
     (rtr
      (for/hash ([(a stack) (in-hash σ)])
        (match stack
          [(cons (cons t vs) stack)
           (values a vs)]
          [_ (values a ∅)]))
      v)))
(mk-mk-imperative/timestamp^-fixpoint
 mk-imperative/timestamp^-fixpoint/stacked restrict-to-reachable/stacked (reset-∆?!))

(define-syntax-rule (with-mutable-worklist body)
  (splicing-syntax-parameterize
   ([yield-meaning yield!])
   body))
(define-syntax-rule (with-mutable-worklist/stacked body)
  (splicing-syntax-parameterize
   ([yield-meaning yield/stacked!])
   body))
(define-syntax-rule (mk-with-store name join join* get get-token)
  (define-syntax-rule (name . body)
    (splicing-syntax-parameterize
        ([bind-join (make-rename-transformer #'join)]
         [bind-join* (make-rename-transformer #'join*)]
         [get-σ-token (make-rename-transformer #'get-token)]
         [getter (make-rename-transformer #'get)])
      . body)))
(mk-with-store with-mutable-store bind-join-h! bind-join*-h! global-hash-getter get-unions)
(mk-with-store with-mutable-store/stacked bind-join-h/stacked! bind-join*-h/stacked! global-hash-getter/stacked get-unions/Δ)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accumulated deltas
(define (*get-unions/Δ)
  (if ∆? (add1 unions) unions))
(define (*get-unions) unions)
(define-syntax-rule (get-unions/Δ σ)
  (*get-unions/Δ))
(define-syntax-rule (get-unions σ)
  (*get-unions))

(define-for-syntax yield/∆s/acc!
  (syntax-rules () [(_ e) (let ([c e])
                            (when (or saw-change?
                                      (not (= unions (hash-ref seen c -1))))
                              (hash-set! seen c unions)
                              (add-todo! c))
                            target-σ)]))
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
      (let ([∆s* (add-∆s ∆s as vss)]) #,(bind-rest #'∆s* #'body)))
    (define-simple-macro* (bind-join (∆s* ∆s a vs) body)
      (let ([∆s* (add-∆ ∆s a vs)]) #,(bind-rest #'∆s* #'body)))))
(mk-add-∆/s add-∆ add-∆s bind-join-∆s/change bind-join*-∆s/change hash-ref)

(define-syntax-rule (with-σ-∆s/acc! body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-∆s/change)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s/change)]
    [get-σ-token (make-rename-transformer #'get-unions/Δ)]
    [yield-meaning yield/∆s/acc!]
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
        (cond [(empty-todo? todo)
               (state-rate)
               (define vs
                 (for*/set ([(c at-unions) (in-hash seen)]
                            #:when (ans^? c))
                   (ans^-v c)))
               (values (format "State count: ~a" (unbox state-count*))
                       (format "Point count: ~a" (hash-count seen))
                       #;
                       global-σ
                       (clean-σ global-σ vs)
                       vs)]
              [else
               (define todo-old todo)
               (set-box! state-count* (+ (unbox state-count) todo-num))
               (reset-todo!)
               (define ∆s (for/append ([c (in-todo todo-old)])
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
(define-syntax-rule (with-σ-∆s! body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e)
                                     (let ([c e])
                                       (when (or saw-change?
                                                 (not (= unions (hash-ref seen c -1))))
                                         (hash-set! seen c unions)
                                         (add-todo! c)))])]
    [bind-join (make-rename-transformer #'bind-join-∆s!)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s!)]
    [get-σ-token (make-rename-transformer #'get-unions/Δ)]
    [getter (make-rename-transformer #'global-hash-getter)])
   body))

(define-syntax-rule (mk-mk-imperative/∆s^-fixpoint mk-name cleaner joiner set-σ! get-σ)
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
        (cond [(empty-todo? todo)
               (state-rate)
               (define vs
                 (for*/set ([(c at-unions) (in-hash seen)]
                            #:when (ans^? c))
                   (ans^-v c)))
               (values (format "State count: ~a" (unbox state-count*))
                       (format "Point count: ~a" (hash-count seen))
                       #;
                       global-σ
                       (clean-σ global-σ vs)
                       vs)]
              [else
               (define todo-old todo)
               (set-box! state-count* (+ (unbox state-count*) todo-num))
               (reset-todo!)
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
               (for ([c (in-todo todo-old)])
                 (reset-saw-change?!)
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
  (set! saw-change? #f)
  (reset-todo!)
  (set! seen (make-hash))
  (set! ∆? #f)
  (set! global-σ σ)
  (set! global-∆s '()))
(define (set-global-σ! v) (set! global-σ v))
(define (reset-todo!)
  (set! todo empty-todo)
  (set! todo-num 0))

(define (prepare-imperative parser sexp)
  (define-values (e renaming) (parser sexp gensym gensym))
  (define e* (add-lib e renaming gensym gensym))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (reset-globals! (make-hash))
  e*)

(define (unbound-addr-error sym addr) (error sym "Unbound address ~a" addr))
(define (bad-stack-error sym addr) (error sym "Internal error: bad stack at address ~a" addr))
(define-syntax-rule (mk-global-store-getter name getter)
  (define-syntax-rule (name σ* a)
    (getter global-σ a (λ () (unbound-addr-error 'name a)))))
(define-syntax-rule (mk-global-store-getter/stacked name getter)
  (define-syntax-rule (name σ* a)
    (match (getter global-σ a (λ () (unbound-addr-error 'name a)))
        [(cons (cons t vs) stack*)
         (if (<= t unions)
             vs
             (match stack*
               [(cons (cons _ vs*) _) vs*]
               [_ (bad-stack-error 'name a)]))]
        [_ (unbound-addr-error 'name a)])))
(mk-global-store-getter global-hash-getter hash-ref)
(mk-global-store-getter/stacked global-hash-getter/stacked hash-ref)
