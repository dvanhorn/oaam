#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "data.rkt" "deltas.rkt" "add-lib.rkt"
         "handle-limits.rkt")
(provide reset-globals! reset-todo! add-todo! inc-unions! set-global-σ!
         mk-mk-imperative/timestamp^-fixpoint
         mk-mk-imperative/∆s/acc^-fixpoint
         mk-mk-imperative/∆s^-fixpoint
         mk-imperative/timestamp^-fixpoint
         mk-imperative/∆s/acc^-fixpoint
         mk-imperative/∆s^-fixpoint
         prepare-imperative
         unions todo seen global-σ
         with-mutable-store
         with-mutable-worklist
         with-σ-∆s/acc!
         with-σ-∆s!)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable global store and worklist.
(define todo #f)
(define seen #f)
(define global-σ #f)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(define unions #f)
(define (inc-unions!) (set! unions (add1 unions)))

(define-for-syntax (yield! stx)
  (syntax-case stx ()
    [(_ e) #'(let ([c e])
               (unless (= unions (hash-ref seen c -1))
                 (hash-set! seen c unions)
                 (add-todo! c)))])) ;; ∪1 → cons

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

(define-syntax-rule (mk-mk-imperative/timestamp^-fixpoint mk-name cleaner)
  (define-syntax-rule (mk-name name ans^? ans^-v touches)
  (define (name step fst)
    (define state-count 0)
    (define clean-σ (cleaner touches))
    (define start-time (current-milliseconds))
    (with-limit-handler (start-time state-count)
      (let loop ()
        (cond [(∅? todo) ;; → null?
               (state-rate start-time state-count)
               (define vs
                 (for*/set ([(c at-unions) (in-hash seen)]
                            #:when (ans^? c))
                   (ans^-v c)))
               (values (format "State count: ~a" state-count)
                       (format "Point count: ~a" (hash-count seen))
                       (clean-σ global-σ vs)
                       vs)]
              [else
               (define todo-old todo)
               (reset-todo!) ;; → '()
               (for ([c (in-set todo-old)])
                 (set! state-count (add1 state-count))
                 (step c)) ;; → in-list
               (loop)]))))))
(mk-mk-imperative/timestamp^-fixpoint
 mk-imperative/timestamp^-fixpoint restrict-to-reachable)

(define-syntax-rule (with-mutable-worklist body)
  (splicing-syntax-parameterize
   ([yield-meaning yield!])
   body))
(define-syntax-rule (with-mutable-store body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-h!)]
    [bind-join* (make-rename-transformer #'bind-join*-h!)]
    [getter (make-rename-transformer #'global-hash-getter)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accumulated deltas
(define-for-syntax yield/∆s/acc!
  (syntax-rules () [(_ e) (begin (add-todo! e)
                                 target-σ)]))

(define-syntax-rule (with-σ-∆s/acc! body)
  (with-σ-∆s
           (splicing-syntax-parameterize
            ([yield-meaning yield/∆s/acc!]
             [getter (make-rename-transformer #'global-hash-getter)])
            body)))

(define-syntax-rule (mk-mk-imperative/∆s/acc^-fixpoint mk-name cleaner)
  (define-syntax-rule (mk-name name ans^? ans^-v touches)
    (define (name step fst)
      ;; fst contains all the ∆s from the first step(s)
      (for ([a×vs (in-list fst)])
        (join-h! (car a×vs) (cdr a×vs)))
      (define state-count 0)
      (define clean-σ (cleaner touches))
      (define start-time (current-milliseconds))
      (with-limit-handler (start-time state-count)
        (let loop ()
          (cond [(∅? todo)
                 (state-rate start-time state-count)
                 (define vs
                   (for*/set ([(c at-unions) (in-hash seen)]
                              #:when (ans^? c))
                     (ans^-v c)))
                 (values (format "State count: ~a" state-count)
                         (format "Point count: ~a" (hash-count seen))
                         (clean-σ global-σ vs)
                         vs)]
                [else
                 (define todo-old todo)
                 (reset-todo!)
                 (set! state-count (set-count todo-old))
                 (define ∆s (for/append ([c (in-set todo-old)]) (step c)))
                 ;; Integrate all the store diffs accumulated over the last
                 ;; frontier steps.
                 (for* ([a×vs (in-list ∆s)]) (join-h! (car a×vs) (cdr a×vs)))
                 (loop)]))))))
(mk-mk-imperative/∆s/acc^-fixpoint
 mk-imperative/∆s/acc^-fixpoint restrict-to-reachable)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Imperative deltas
(define global-∆s #f)
(define (add-∆! a vs) (set! global-∆s (cons (cons a vs) global-∆s)))
(define (add-∆s! as vss)
  (set! global-∆s (for/fold ([acc global-∆s])
                      ([a (in-list as)]
                       [vs (in-list vss)])
                    (cons (cons a vs) acc))))
(define-simple-macro* (bind-join-∆s! (∆s* ∆s a vs) body)
  (begin (add-∆! a vs) body))
(define-simple-macro* (bind-join*-∆s! (∆s* ∆s as vss) body)
  (begin (add-∆s! as vss) body))

(define-syntax-rule (with-σ-∆s! body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (add-todo! e)])]
    [bind-join (make-rename-transformer #'bind-join-∆s!)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s!)]
    [getter (make-rename-transformer #'global-hash-getter)])
   body))

(define-syntax-rule (mk-mk-imperative/∆s^-fixpoint mk-name cleaner)
  (define-syntax-rule (mk-name name ans^? ans^-v touches)
    (define (name step fst)
      ;; fst contains all the ∆s from the first step(s)
      (for ([a×vs (in-list fst)])
        (join-h! (car a×vs) (cdr a×vs)))
      (define state-count 0)
      (define clean-σ (cleaner touches))
      (define start-time (current-milliseconds))
      (with-limit-handler (start-time state-count)
        (let loop ()
          (cond [(∅? todo)
                 (state-rate start-time state-count)
                 (define vs
                   (for*/set ([(c at-unions) (in-hash seen)]
                              #:when (ans^? c))
                     (ans^-v c)))
                 (values (format "State count: ~a" state-count)
                         (format "Point count: ~a" (hash-count seen))
                         (clean-σ global-σ vs)
                         vs)]
                [else
                 (define todo-old todo)
                 (reset-todo!)
                 (set! state-count (set-count todo-old))
                 (for ([c (in-set todo-old)]) (step c))
                 ;; Integrate all the store diffs accumulated over the last
                 ;; frontier steps.
                 (for* ([a×vs (in-list global-∆s)]) (join-h! (car a×vs) (cdr a×vs)))
                 (reset-∆s!)
                 (loop)]))))))
(mk-mk-imperative/∆s^-fixpoint
  mk-imperative/∆s^-fixpoint restrict-to-reachable)

(define (reset-∆s!) (set! global-∆s '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common functionality
(define (reset-globals! σ)
  (set! unions 0)
  (set! todo ∅)
  (set! seen (make-hash))
  (set! global-σ σ)
  (set! global-∆s '()))
(define (set-global-σ! v) (set! global-σ v))
(define (reset-todo!) (set! todo ∅))
(define (add-todo! c) (set! todo (∪1 todo c)))

(define (prepare-imperative parser sexp)
  (define-values (e renaming) (parser sexp gensym gensym))
  (define e* (add-lib e renaming gensym gensym))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (reset-globals! (make-hash))
  e*)

(define-syntax-rule (global-hash-getter σ* a)
  (hash-ref global-σ a (λ () (error 'global-hash-getter "Unbound address ~a" a))))
