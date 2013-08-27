#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         (for-syntax racket/syntax syntax/parse "notation.rkt" racket/match)
         (only-in "store-passing.rkt" bind-rest with-whole-μ)
         "data.rkt" "deltas.rkt" "add-lib.rkt"
         (only-in "ast.rkt" var?)
         "handle-limits.rkt"
         (only-in "tcon.rkt" Γτ)
         "graph.rkt"
         "goedel-hash.rkt"
         "struct-copy.rkt"
         racket/unsafe/ops
         racket/trace)
(provide reset-globals! reset-todo! add-todo! inc-unions! set-global-σ! set-global-μ!
         saw-change! saw-change? push-Ξ! memo!
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
         unions todo seen global-σ global-μ global-Ξ global-M
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
(define global-Ξ #f)
(define global-M #f)
(define ∆? #f)
(define (set-∆?!) (set! ∆? #t))
(define (reset-∆?!) (when ∆? (inc-unions!) (set! ∆? #f)))
(define (reset-pushdown!) (set! global-Ξ (make-hash)) (set! global-M (make-hash)))
(define (push-Ξ! ctx k) (hash-join1! global-Ξ ctx k))
(define (memo! ctx vs) (hash-join! global-M ctx vs))

(define empty-todo '())
(define empty-todo/set ∅)
(define empty-todo? null?)
(define empty-todo/set? ∅?)
(define (add-todo! c)
  (set! todo (cons c todo))
  (set! todo-num (add1 todo-num)))
(define (add-todo/set! c)
  (set! todo (∪1 todo c))
  (set! todo-num (add1 todo-num)))
(define-syntax (mk-add-todo/guard stx)
  (syntax-parse stx
   [(_ name state-base point (co dr chk ans ap ev cc)
       touches root reach*
       (~optional (~and (~or #:husky #:narrow)
                        kind)))
    (define μ? (syntax-parameter-value #'abs-count?))
    (define compiledv? (syntax-parameter-value #'compiled?))
    (define kindv (and (attribute kind) (syntax-e #'kind)))
    (define-syntax ifμ
      (syntax-rules ()
        [(_ t) (if μ? (list t) '())]
        [(_ t e) (if μ? t e)]))
    (head*
     define/with-syntax
     [state-base: (format-id #'state-base "~a:" #'state-base)]
     [state-base-rσ (format-id #'state-base "~a-rσ" #'state-base)]
     [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
     [set-state-base-rσ! (format-id #'state-base "set-~a-rσ!" #'state-base)]
     [point-τ (format-id #'point "~a-τ" #'point)]
     [point-μ (format-id #'point "~a-μ" #'point)]
     [point-conf (format-id #'point "~a-conf" #'point)]
     [(μ-op ...) (if μ? #'(μ*) #'())])
    (define def-c*
      (syntax/loc stx
        (define c*
          (syntax-parameterize ([target-σ (make-rename-transformer #'σ*)])
            (state-base pnt*)))))
    (quasisyntax/loc stx
     (begin
       (define (name c)
         (define σ (or (and current-state (state-base-rσ current-state)) empty-σ))
         #,@(if-μ #'(define μ (point-μ (state-base-pnt c))))
         (define-values (∆s pnt)
           (values (state-base-rσ c) (state-base-pnt c)))
         #,@(if-μ #'(define μ* (point-μ pnt)))
         (define-values (τ conf) (values (point-τ pnt) (point-conf pnt)))
         (define-values (σ* τ* #,@(if-μ #'μ**))
           (let ()
             #,@(cond
                 [(syntax-parameter-value #'σ-∆s?)
                  (define do-Γ
                    #`( ;; It is possible that we add values that reference addresses that only
                       ;; are 
                       ;;(define root-σ (update ∆s σ))
                       (define reachable-addresses (reach* σ (∪ (root c)
                                                                (for/union ([p (in-list ∆s)])
                                                                  (touches (cdr p))))))
                       #;#;#;#;(printf "Reachable addresses ~a~%" reachable-addresses)
                       (define killed (for/set ([k (in-hash-keys σ)]
                       #:unless (k . ∈ . reachable-addresses))
                       k))
                       (when (`(A . g80) . ∈ . killed) (pretty-print global-Ξ))
                       (printf "Killed addresses ~a~%" killed)
                       (values (update ∆s (restrict-σ-to-set σ reachable-addresses))
                               (Γτ reachable-addresses touches τ)
                               #,@(if-μ (syntax/loc stx (restrict-hash-to-set μ* reachable-addresses))))))
                    (if-μ
                     (quasisyntax/loc stx
                       ((cond
                         ;; If before updating the address, the count is > 0, try to GC.
                         [(for/or ([p (in-list ∆s)]) (not (eq? 0 (hash-ref μ (car p) 0))))
                          #,@do-Γ]
                         [else
                          (printf "Skipping GC ~a~%" ∆s)
                          (values (update ∆s σ) τ μ*)])))
                     do-Γ)]
                  [(and (attribute kind)
                        (eq? '#:husky (syntax-e #'kind)))
                   (raise-syntax-error 'mk-add-todo/guard "Todo" stx)]
                  [else
                   (quasisyntax/loc stx
                     ((define reachable-addresses (reach* ∆s (root c)))
                      #;
                      (when (for/or ([a (in-hash-keys τ)]
                                     #:when (a . ∉ . reachable-addresses))
                              (and (pair? a) (eq? 'η (car a))))
                        (pretty-print global-Ξ)
                        (newline)
                        (pretty-print reachable-addresses)
                        (pretty-print c)
                        (error 'Γ "Killed monitor"))
                      (values (restrict-σ-to-set ∆s reachable-addresses)
                              (Γτ reachable-addresses touches τ)
                              #,@(if-μ (syntax/loc stx (restrict-hash-to-set μ* reachable-addresses))))))])))
           (define pnt*
             (syntax-parameterize ([target-τ (make-rename-transformer #'τ*)]
                                   [target-μ (make-rename-transformer #'μ**)])
               (point conf)))
#;           (printf "Point ~a~%Store ~a~%" pnt* σ*)
           #,@(case kindv
                [(#f) (raise-syntax-error #f "Wide GC? What are you, nuts?" stx)]
                [(#:husky)
                 (quasisyntax/loc stx
                   ((match (hash-ref seen pnt* #f)
                      [#f #,def-c*
                          (add-todo/set! c*)
                          (hash-set! seen pnt* c* #;(cons 0 c*)
                                     )] ;; start a new store count since this is a new point.
                      [(and sb (state-base: σ _)) #;(cons σt (and sb (state-base: σ _)))
                       ;; We add σ* to σ (crucially in this order)
                       ;; If there are any changes since last visit,
                       ;; we re-add the state to process and continue propagating
                       ;; TODO: Is this sound for abstract counting?
                       (define-values (σ** same?) (join-store/change σ σ*))
                       (define rng (for/union ([vs (in-hash-values σ**)]) (touches vs)))
                       (define rng* (for/union ([vs (in-hash-values σ*)]) (touches vs)))
                       (define zombies (for/set ([a (in-set (set-subtract rng (list->set (hash-keys σ**))))]
                                                 #:unless (and (pair? a) (eq? (car a) 'η)))
                                         a))
                       (define zombies* (for/set ([a (in-set (set-subtract rng* (list->set (hash-keys σ*))))]
                                                  #:unless (and (pair? a) (eq? (car a) 'η)))
                                          a))
                       (unless (and (∅? zombies) (∅? zombies*))
                         (error 'Γ "Zombies! ~a, ~a" zombies zombies*))
                       (unless same?
                         (set-state-base-rσ! sb σ**)
                         (add-todo/set! sb))])))]
                [(#:narrow)
                 ;; Narrow
                 (quasisyntax/loc stx
                   (#,def-c*
                     (unless (hash-has-key? seen c*)
                       (add-todo/set! c*)
                       (hash-set! seen c* #t))))]))
       #;
         (trace name)))]))

   (define-syntax in-todo (make-rename-transformer #'in-list))
   (define-syntax in-todo/set (make-rename-transformer #'in-set))

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
   (define-simple-macro* (mk-bind-μbump name name* μbump)
(begin
  (define-syntax-rule (name (a) . body)
    (let () #,@(if-μ #'(μbump a)) . body))
  (define-syntax-rule (name* (as) . body)
    (let () #,@(if-μ #'(for-each μbump as)) . body))))
   (define-simple-macro* (mk-joiner name getter setter μbump)
(define (name a vs)
  (define prev (getter global-σ a nothing))
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
   (define-simple-macro* (mk-joiner/stacked name getter setter)
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
    [sv (error 'name "Bad store value at ~a: ~a" a sv)])))
   (mk-μbump μbump-h! hash-ref hash-set!)
   (mk-joiner join-h! hash-ref hash-set! μbump-h!)
   (mk-μbump/stacked μbump-h/stacked! hash-ref hash-set!)
   (mk-joiner/stacked join-h/stacked! hash-ref hash-set!)
   (mk-bind-joiner bind-join-h! join-h!)
   (mk-bind-joiner bind-join-h/stacked! join-h/stacked!)
   (mk-bind-μbump bind-μbump-h! bind-μbump*-h! μbump-h!)
   (mk-bind-μbump bind-μbump-h/stacked! bind-μbump*-h/stacked! μbump-h/stacked!)
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
                   [point-conf (format-id #'point "~a-conf" #'point)]
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
               (cond [(empty-todo? todo)
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
                                   [pnt (in-value (state-base-pnt c))]
                                   [conf (in-value (point-conf pnt))]
                                   #:when (ans^? conf))
                          (list (ans^-v conf) (point-τ pnt))))
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
                      (reset-todo!)
                      (for ([c (in-todo todo-old)])
                        #,@(if-graph #'(current-state! c))
                        (step c))
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
        [_ (values a nothing)]))
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
   (define-syntax-rule (mk-with-store name join join* μbump μbump* get μget)
(define-syntax-rule (name . body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'join)]
    [bind-join* (make-rename-transformer #'join*)]
    [bind-μbump (make-rename-transformer #'μbump)]
    [bind-μbump* (make-rename-transformer #'μbump*)]
    [getter (make-rename-transformer #'get)]
    [μgetter (make-rename-transformer #'μget)])
   . body)))
   (mk-with-store with-mutable-store
bind-join-h!
bind-join*-h!
bind-μbump-h!
bind-μbump*-h!
global-hash-getter
global-hash-μgetter)
   (mk-with-store with-mutable-store/stacked
bind-join-h/stacked!
bind-join*-h/stacked!
bind-μbump-h/stacked!
bind-μbump*-h/stacked!
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

   (define-syntax-rule (mk-mk-imperative/∆s/acc^-fixpoint mk-name cleaner joiner set-σ! get-σ)
(define-syntax (mk-name stx)
  (syntax-case stx ()
    [(_ name state-base point ans^ touches)
     (with-syntax ([ans^? (format-id #'ans^ "~a?" #'ans^)]
                   [ans^-v (format-id #'ans^ "~a-v" #'ans^)]
                   [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
                   [point-τ (format-id #'point "~a-τ" #'point)]
                   [point-conf (format-id #'point "~a-conf" #'point)])
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
                                   [pnt (in-value (state-base-pnt c))]
                                   [conf (in-value (point-conf pnt))]
                                   #:when (ans^? conf))
                          (list (ans^-v conf) (point-τ pnt))))
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
                        (set-σ! global-σ a (⊓ (get-σ global-σ a nothing) (cdr a×vs))))
                      ;; Only one inc needed since all updates are synced.
                      (unless (null? ∆s) (inc-unions!))
                      (loop)])))))])))
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
  [getter (make-rename-transformer #'global-hash-getter)]
  [imperative? #t])
 body))

   (define-syntax-rule (mk-mk-imperative/∆s^-fixpoint mk-name cleaner joiner set-σ! get-σ)
(define-syntax (mk-name stx)
  (syntax-case stx ()
    [(_ name state-base point ans^ touches)
     (with-syntax ([ans^? (format-id #'ans^ "~a?" #'ans^)]
                   [ans^-v (format-id #'ans^ "~a-v" #'ans^)]
                   [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
                   [point-τ (format-id #'point "~a-τ" #'point)]
                   [point-conf (format-id #'point "~a-conf" #'point)])
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
                                   [pnt (in-value (state-base-pnt c))]
                                   [conf (in-value (point-conf pnt))]
                                   #:when (ans^? conf))
                          (list (ans^-v conf) (point-τ pnt))))
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
                        (set-σ! global-σ a (⊓ (get-σ global-σ a nothing) (cdr a×vs))))
                      ;; Only one inc needed since all updates are synced.
                      (unless (null? global-∆s) (inc-unions!))
                      (reset-∆s!)
                      (loop)])))))])))
   (mk-mk-imperative/∆s^-fixpoint
mk-imperative/∆s^-fixpoint restrict-to-reachable join-h! hash-set! hash-ref)

   (define (reset-∆s!) (set! global-∆s '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Imperative husky deltas with GC (not wide, but not narrow)
(define-syntax (with-timestamp-∆-fix/Γ stx)
  (syntax-parse stx
    [(_ [state-base point (co dr chk ans ap cc ev) touches root
                    (~or (~optional (~and #:compiled compiled?))
                         (~optional (~and
                                     kind
                                     (~or #:narrow #:husky)))) ...]
        body ...)
     (define kindv (and (attribute kind) (syntax-e #'kind)))
     (head*
      define/with-syntax
      [ans? (format-id #'ans "~a?" #'ans)]
      [ans-v (format-id #'ans "~a-v" #'ans)]
      [state-base-rσ (format-id #'state-base "~a-rσ" #'state-base)]
      [state-base-pnt (format-id #'state-base "~a-pnt" #'state-base)]
      [point-conf (format-id #'point "~a-conf" #'point)]
      [(μ-op ...) (if-μ #'μ*)])
     (quasisyntax/loc stx
       (begin
         (define-syntax-rule (internal-fixpoint step fst)
           (let ()
             (set-box! (start-time) (current-milliseconds))
             (define state-count* (state-count))
             (define states-last 0)
             (set-box! state-count* 0)
             (reset-todo/set!)
             (printf "Init~%")
             (init-GH!)
             (reset-pushdown!)
             (set-seen! (make-hash)) ;; point → (state-base σ μ (point τ conf))
             fst
             (let loop ()
               (cond [(empty-todo/set? todo)
                      (set-box! state-count* (hash-count seen))
                      (state-rate)
                      (for*/set (#,(case kindv
                                     [(#f) (raise-syntax-error #f "Wide GC?" stx)]
                                     [(#:husky) #'[c (in-hash-values seen)]]
                                     [(#:narrow) #'[c (in-hash-keys seen)]])
                                 [pnt (in-value (state-base-pnt c))]
                                 [conf (in-value (point-conf pnt))]
                                 #:when (ans? conf))
                        (list (state-base-rσ c)
                              (ans-v conf)))]
                     [else
                      (define todo-old todo)
                      (define new-state-count* (+ (unbox state-count*) todo-num))
                      (set-box! state-count* new-state-count*)
                      (reset-todo/set!)
                      (for ([c (in-todo/set todo-old)])
                        (current-state! c)
                        (step c))
                      (loop)]))))
         (splicing-syntax-parameterize
          ([fixpoint (make-rename-transformer #'internal-fixpoint)]
           [yield-meaning (mk-yield #'internal-yielder)]
           [imperative? #t]
           [global-σ? #f])
          body ...
          (mk-add-todo/guard internal-yielder state-base point (co dr chk ans ap cc ev) touches root reach*
                             #,@(if (attribute kind) #'(kind) '()))
          ;; must be down here so that touches is defined.
          (define reach* (reach touches)))))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common functionality
   (define (reset-globals! σ μ)
(set! unions 0)
(set! saw-change? #f)
(reset-pushdown!)
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
   (define (reset-todo/set!)
(set! todo empty-todo/set)
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
