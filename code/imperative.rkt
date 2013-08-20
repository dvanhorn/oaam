#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         (for-syntax racket/syntax syntax/parse "notation.rkt")
         (only-in "store-passing.rkt" bind-rest) "data.rkt" "deltas.rkt" "add-lib.rkt"
         (only-in "ast.rkt" var?)
         "handle-limits.rkt"
         (only-in "tcon.rkt" Γτ)
         "graph.rkt"
         "struct-copy.rkt"
         racket/unsafe/ops)
(provide reset-globals! reset-todo! add-todo! inc-unions! set-global-σ! set-global-μ!
         saw-change!
         reset-saw-change?!
         mk-mk-imperative/timestamp^-fixpoint
         mk-mk-imperative/∆s/acc^-fixpoint
         mk-mk-imperative/∆s^-fixpoint
         mk-imperative/timestamp^-fixpoint
         mk-imperative/timestamp^-fixpoint/stacked
         mk-imperative/∆s/acc^-fixpoint
         mk-imperative/∆s^-fixpoint
         with-timestamp-∆-fix/Γ
         mk-add-∆/s
         mk-add-∆/s!
         mk-join* mk-joiner mk-μbump mk-μbump/stacked mk-bind-μbump
         mk-joiner/stacked mk-bind-joiner
         mk-global-store-getter
         mk-global-μ-getter
         mk-with-store
         mk-global-store-getter/stacked
         mk-global-μ-getter/stacked
         reset-∆?!
         prepare-imperative
         unions todo seen global-σ global-μ
         with-mutable-store
         with-mutable-store/stacked
         with-mutable-worklist^
         with-mutable-worklist/stacked^
         with-σ-∆s/acc!
         with-σ-∆s!)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable global store and worklist.
(define todo #f) (define todo-num 0)
(define seen #f) (define (set-seen! v) (set! seen v))
(define global-σ #f)
(define global-μ #f)
(define ∆? #f)
(define (set-∆?!) (set! ∆? #t))
(define (reset-∆?!) (when ∆? (inc-unions!) (set! ∆? #f)))

(define empty-todo '())
(define empty-todo? null?)
(define (add-todo! c)
  (set! todo (cons c todo))
  (set! todo-num (add1 todo-num)))
(define-simple-macro* (mk-add-todo/guard name state-base point (co dr chk ans ap ev cc) touches root reach*)
  #,(let ()
      (define μ? (syntax-parameter-value #'abs-count?))
      (define compiledv? (syntax-parameter-value #'compiled?))
      (define-syntax ifμ
        (syntax-rules ()
          [(_ t) (if μ? (list t) '())]
          [(_ t e) (if μ? t e)]))
      (head*
       define/with-syntax
       [state-base-rσ (format-id #'state-base "~a-rσ" #'state-base)]
       [state-base-μ (format-id #'state-base "~a-μ" #'state-base)]
       [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
       [point-τ (format-id #'point "~a-τ" #'point)]
       [point-conf (format-id #'point "~a-conf" #'point)]
       [(μ-op ...) (if μ? #'(μ*) #'())])
      #`(define (name c)
          (define σ (or (and current-state (state-base-rσ current-state)) σ₀))
          #,@(if-μ #'(define μ (state-base-μ c)))
          (define-values (∆s μ-op ... pnt)
            (values (state-base-rσ c)
                    #,@(if-μ #'(state-base-μ c))
                    (state-base-pnt c)))
          (define-values (τ conf) (values (point-τ pnt) (point-conf pnt)))
          (define-values (σ* τ* #,@(if-μ #'μ**))
            #,(if-μ
               #'(cond
                  [(for/or ([p (in-list ∆s)]) (not (eq? 0 (hash-ref μ (car p) 0))))
                   (define reachable-addresses (reach* σ (root c)))
                   (values (update ∆s (restrict-to-set σ reachable-addresses))
                           (Γτ reachable-addresses touches τ)
                           (restrict-to-set μ* reachable-addresses))]
                  [else (values (update ∆s σ) τ μ*)])
               #'(values (update ∆s σ) τ μ*)))
          (define c*
            (syntax-parameterize ([target-τ (make-rename-transformer #'τ*)]
                                  [target-σ (make-rename-transformer #'σ*)]
                                  [target-μ (make-rename-transformer #'μ**)])
             (state-base (point conf))))
          (unless (hash-has-key? seen c*)
            (add-todo! c*)
            (hash-set! seen c* #t)))))

(define-syntax in-todo (make-rename-transformer #'in-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(define unions #f)
(define (inc-unions!) (set! unions (add1 unions)))

(define (do-yield^! c)
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

(define current-state #f)
(define graph #f) (define (set-graph! g) (set! graph g))
(define (current-state! s) (set! current-state s))
(define-syntax (emit-edge! stx)
  (syntax-case stx ()
    [(_ e) #`(begin #,@(if-graph #'(add-edge! graph current-state e)))]))
(define-for-syntax ((mk-yield yielder) stx)
  (syntax-case stx () [(_ e) #`(let ([s e]) (emit-edge! s) (reset-kind!) (#,yielder s))]))
(define-for-syntax yield^! (mk-yield #'do-yield^!))
(define-for-syntax yield! (mk-yield #'add-todo/guard!))
(define-for-syntax yield/stacked! (mk-yield #'do-yield/stacked!))

(define-simple-macro* (mk-bind-joiner name joiner)
  (define-syntax-rule (name (a vs) . body)
    (let () (joiner a vs) . body)))
(define-simple-macro* (mk-bind-μbump name μbump)
  (define-syntax-rule (name (a) . body)
    (let () #,@(if-μ #'(μbump a)) . body)))
(define-simple-macro* (mk-joiner name getter setter μbump)
  (define (name a vs)
    (define prev (getter global-σ a ∅))
    (define upd (⊓ vs prev))
    #,@(if-μ #'(μbump a))
    (unless (≡ prev upd)
      (setter global-σ a upd)
      (inc-unions!))))
(define-syntax-rule (mk-join* name joiner)
  (define (name as vss)
    (for ([a (in-list as)]
          [vs (in-list vss)])
      (joiner a vs))))

(define-syntax-rule (mk-μbump name μgetter μsetter)
  (define (name a)
    (μsetter global-μ a (μinc (μgetter global-μ a 0)))))
(define-simple-macro* (mk-μbump/stacked name μgetter μsetter)
  (define (name a)
    #,@(if-μ
        #'(define (μadd t n stack)
            (μsetter global-μ a (cons (cons t n) stack))))
    #,(if-μ #'(match (μgetter global-μ a)
                ['() (μsetter a (list (cons unions* 1)))]
                [(and μstack (cons (cons t* n) μstack*))
                 (unless (eq? n '∞)
                   (if (< t unions)
                       (μadd (add1 unions) (μinc n) μstack)
                       (μadd t* (μinc n) μstack*)))])
            #'(void))))
(define-simple-macro* (mk-joiner/stacked name getter setter μbump)
  (define (name a vs)
    (define (add t vs stack)
      (set-∆?!)
      (setter global-σ a (cons (cons t vs) stack)))
    (match (getter global-σ a '())
      ['()
       (define unions* (add1 unions))
       (add unions* vs '())]
      [(and stack (cons (cons t vs*) stack*))
       (define upd (⊓ vs vs*))
       (unless (≡ upd vs*)
         (if (< t unions)
             (add (add1 unions) upd stack)
             (add t upd stack*)))]
      [sv (error 'name "Bad store value at ~a: ~a" a sv)])
    #,@(if-μ #'(μbump a))))
(mk-μbump μbump-h! hash-ref hash-set!)
(mk-joiner join-h! hash-ref hash-set! μbump-h!)
(mk-μbump/stacked μbump-h/stacked! hash-ref hash-set!)
(mk-joiner/stacked join-h/stacked! hash-ref hash-set! μbump-h/stacked!)
(mk-bind-joiner bind-join-h! join-h!)
(mk-bind-joiner bind-join-h/stacked! join-h/stacked!)
(mk-bind-μbump bind-μbump-h! μbump-h!)
(mk-bind-μbump bind-μbump-h/stacked! μbump-h/stacked!)
(mk-join* join*-h! join-h!)
(mk-join* join*-h/stacked! join-h/stacked!)
(mk-bind-joiner bind-join*-h! join*-h!)
(mk-bind-joiner bind-join*-h/stacked! join*-h/stacked!)


(define-syntax-rule (mk-mk-imperative/timestamp^-fixpoint mk-name cleaner extra-reset)
  (define-syntax (mk-name stx)
    (syntax-parse stx
      [(_ name state-base point ans^ touches #:ev ev #:co co (~optional (~and #:compiled compiled?)))
       (with-syntax ([ans^? (format-id #'ans^ "~a?" #'ans^)]
                     [ans^-v (format-id #'ans^ "~a-v" #'ans^)]
                     [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
                     [point-τ (format-id #'point "~a-τ" #'point)]
                     [ev? (format-id #'ev "~a?" #'ev)]
                     [ev-e (format-id #'ev "~a-e" #'ev)]
                     [co? (format-id #'co "~a?" #'co)])
         #`(define-syntax-rule (name step fst)
             (let ()
               #,@(if-graph #'(set-graph! (make-hash)))
               (set-box! (start-time) (current-milliseconds))
               fst
               (define state-count* (state-count))
               (set-box! state-count* 0)
               (define clean-σ (cleaner touches))
               (let loop ()
                 (cond [(empty-todo? todo) ;; → null?
                        (state-rate)
                        #,@(if-graph #`(dump-dot graph
                                                 #,(if (syntax-e #'compiled?)
                                                       #'(λ _ #f)
                                                       #'(λ (s) (and (ev? s) (var? (ev-e s)))))
                                                 #,(if (syntax-e #'compiled?)
                                                       #'(λ _ #f)
                                                       #'ev?)
                                                 co? compiled?))
                        (define vs
                          (for*/set ([(c at-unions) (in-hash seen)]
                                     #:when (ans^? c))
                            (cons (ans^-v c) (point-τ (state-base-pnt c)))))
                        (values (format "State count: ~a" (unbox state-count*))
                                (format "Point count: ~a" (hash-count seen))
                                (with-output-to-string
                                  (λ ()
                                     (pretty-print
                                      (for/list ([i (in-naturals)]
                                                 [lst (in-vector global-σ)]
                                                 #:unless (null? lst))
                                        (list i lst)))))
                     #;           (clean-σ global-σ (set-map car vs))
                                vs)]
                       [else
                        (define todo-old todo)
                        extra-reset
                        (set-box! state-count* (+ (unbox state-count*) todo-num))
                        (reset-todo!) ;; → '()
                        (for ([c (in-todo todo-old)])
                          #,@(if-graph #'(current-state! c))
                          (step c)) ;; → in-list
                        (loop)])))))])))
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

(define-syntax-rule (with-mutable-worklist^ body)
  (splicing-syntax-parameterize
   ([yield-meaning yield^!]
    [imperative? #t])
   body))
(define-syntax-rule (with-mutable-worklist/stacked^ body)
  (splicing-syntax-parameterize
   ([yield-meaning yield/stacked!]
    [imperative? #t])
   body))
(define-syntax-rule (mk-with-store name join join* μbump get μget)
  (define-syntax-rule (name . body)
    (splicing-syntax-parameterize
        ([bind-join (make-rename-transformer #'join)]
         [bind-join* (make-rename-transformer #'join*)]
         [bind-μbump (make-rename-transformer #'μbump)]
         [getter (make-rename-transformer #'get)]
         [μgetter (make-rename-transformer #'μget)])
      . body)))
(mk-with-store with-mutable-store
               bind-join-h!
               bind-join*-h!
               bind-μbump-h!
               global-hash-getter
               global-hash-μgetter)
(mk-with-store with-mutable-store/stacked
               bind-join-h/stacked!
               bind-join*-h/stacked!
               bind-μbump-h/stacked!
               global-hash-getter/stacked
               global-hash-μgetter/stacked)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accumulated deltas
(define-for-syntax yield/∆s/acc!
  (syntax-rules () [(_ e) (let ([c e])
                            (when (or saw-change?
                                      (not (= unions (hash-ref seen c -1))))
                              (hash-set! seen c unions)
                              (add-todo! c))
                            target-σ)]))
(define-simple-macro* (mk-add-∆/s add-∆ add-∆s bind-join bind-join* get-σ)
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
    [yield-meaning yield/∆s/acc!]
    [getter (make-rename-transformer #'global-hash-getter)]
    [μgetter (make-rename-transformer #'global-hash-μgetter)])
   body))

(define-syntax-rule (mk-mk-imperative/∆s/acc^-fixpoint mk-name cleaner joiner set-σ! get-σ μbump)
  (define-syntax (mk-name stx)
    (syntax-case stx ()
      [(_ name state-base point ans^ touches)
       (with-syntax ([ans^? (format-id #'ans^ "~a?" #'ans^)]
                     [ans^-v (format-id #'ans^ "~a-v" #'ans^)]
                     [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
                     [point-τ (format-id #'point "~a-τ" #'point)])
         #'(define-syntax-rule (name step fst)
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
                            (cons (ans^-v c) (point-τ (state-base-pnt c)))))
                        (values (format "State count: ~a" (unbox state-count*))
                                (format "Point count: ~a" (hash-count seen))
                                #;
                                global-σ
                                (clean-σ global-σ (set-map car vs))
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
                          #,@(if-μ #'(μbump a))
                          (set-σ! global-σ a (⊓ (get-σ global-σ a nothing) (cdr a×vs))))
                        ;; Only one inc needed since all updates are synced.
                        (unless (null? ∆s) (inc-unions!))
                        (loop)])))))])))
(mk-mk-imperative/∆s/acc^-fixpoint
 mk-imperative/∆s/acc^-fixpoint restrict-to-reachable join-h! hash-set! hash-ref μbump-h!)
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
    [getter (make-rename-transformer #'global-hash-getter)]
    [imperative? #t])
   body))

(define-syntax-rule (mk-mk-imperative/∆s^-fixpoint mk-name cleaner joiner set-σ! get-σ μbump)
  (define-syntax (mk-name stx)
    (syntax-case stx ()
      [(_ name state-base point ans^ touches)
       (with-syntax ([ans^? (format-id #'ans^ "~a?" #'ans^)]
                     [ans^-v (format-id #'ans^ "~a-v" #'ans^)]
                     [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
                     [point-τ (format-id #'point "~a-τ" #'point)])
         #'(define-syntax-rule (name step fst)
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
                            (cons (ans^-v c) (point-τ (state-base-pnt c)))))
                        (values (format "State count: ~a" (unbox state-count*))
                                (format "Point count: ~a" (hash-count seen))
                                #;
                                global-σ
                                (clean-σ global-σ (map car vs))
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
                          #,@(if-μ #'(μbump a))
                          (set-σ! global-σ a (⊓ (get-σ global-σ a nothing) (cdr a×vs))))
                        ;; Only one inc needed since all updates are synced.
                        (unless (null? global-∆s) (inc-unions!))
                        (reset-∆s!)
                        (loop)])))))])))
(mk-mk-imperative/∆s^-fixpoint
  mk-imperative/∆s^-fixpoint restrict-to-reachable join-h! hash-set! hash-ref μbump-h!)

(define (reset-∆s!) (set! global-∆s '()))

(define σ₀ (hash))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Imperative narrow deltas with GC
(define-simple-macro* (with-timestamp-∆-fix/Γ [state-base point (co dr chk ans ap cc ev) touches root
                                                          (~optional (~and #:compiled compiled?))]
                                       body ...)
  #,(with-syntax ([ans? (format-id #'ans "~a?" #'ans)]
                  [(μ-op ...) (if-μ #'μ*)])
      #`(begin
          (define-syntax-rule (internal-fixpoint step fst)
            (let ()             
             (set-box! (start-time) (current-milliseconds))
             (define state-count* (state-count))
             (define states-last 0)
             (set-box! state-count* 0)
             (reset-todo!) ;; → '()
             (set-seen! (make-hash))
 ;            (printf "Frist~%")
             fst
             (let loop ()
               (cond [(empty-todo? todo)
                      (set-box! state-count* (hash-count seen))
                      (state-rate)
                      ;; TODO: Some report here
                      ]
                     [else
                      (define todo-old todo)
                      (define new-state-count* (+ (unbox state-count*) todo-num))
                      (set-box! state-count* new-state-count*)
                      (when (> (- new-state-count* states-last) 1000)
                        (printf "States: ~a~%" new-state-count*)
                        (set! states-last new-state-count*))
                      (reset-todo!)
                      (for ([c (in-todo todo-old)])
                        (current-state! c)
;                        (printf "Stepping ~a~%" c)
                        (step c))
                      (loop)]))))
          (mk-add-todo/guard internal-yielder state-base point (co dr chk ans ap cc ev) touches root reach*)
          (splicing-syntax-parameterize
           ([fixpoint (make-rename-transformer #'internal-fixpoint)]
            [yield-meaning (mk-yield #'internal-yielder)]
            [imperative? #t])
            body ...
            (define reach* (reach touches))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common functionality
(define (reset-globals! σ μ)
  (set! unions 0)
  (set! saw-change? #f)
  (reset-todo!)
  (set! seen (make-hash))
  (set! ∆? #f)
  (set! global-σ σ)
  (set! global-μ μ)
  (set! global-∆s '()))
(define (set-global-σ! v) (set! global-σ v))
(define (set-global-μ! v) (set! global-μ v))
(define (reset-todo!)
  (set! todo empty-todo)
  (set! todo-num 0))
(define (set-todo! v) (set! todo v))

(define (prepare-imperative parser sexp)
  (define-values (e renaming) (parser sexp gensym gensym))
  (define e* (add-lib e renaming gensym gensym))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (reset-globals! (make-hash) (make-hash))
  e*)

(define (unbound-addr-error sym addr) (error sym "Unbound address ~a" addr))
(define (bad-stack-error sym addr) (error sym "Internal error: bad stack at address ~a" addr))
(define-syntax-rule (mk-global-getter name target getter a get-default)
  (define-syntax-rule (name a)
    (getter target a get-default)))
(define-syntax-rule (mk-global-store-getter name target getter)
  (mk-global-getter name target getter a (λ () (unbound-addr-error 'name a))))
(define-syntax-rule (mk-global-μ-getter name target getter)
  (mk-global-getter name target getter a 0))
(define-syntax-rule (mk-global-getter/stacked name target getter a get-default get-fail)
  (define-syntax (name stx)
    (syntax-case stx ()
      [(_ a)
       (syntax/loc stx
         (match (getter target a get-default)
           [(cons (cons t vs) stack*)
            (if (<= t unions)
                vs
                (match stack*
                  [(cons (cons _ vs*) _) vs*]
                  [_ (bad-stack-error 'name a)]))]
           [_ get-fail]))]
      [name (syntax/loc stx (λ (a) (name a)))])))
(define-syntax-rule (mk-global-store-getter/stacked name target getter)
  (mk-global-getter/stacked name target getter a
                            (λ () (unbound-addr-error 'name a))
                            (unbound-addr-error 'name a)))
(define-syntax-rule (mk-global-μ-getter/stacked name target getter)
  (mk-global-getter/stacked name target getter a #f 0))
(mk-global-store-getter global-hash-getter global-σ hash-ref)
(mk-global-μ-getter global-hash-μgetter global-μ hash-ref)
(mk-global-store-getter/stacked global-hash-getter/stacked global-σ hash-ref)
(mk-global-μ-getter/stacked global-hash-μgetter/stacked global-μ hash-ref)
