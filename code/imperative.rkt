#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "data.rkt" "add-lib.rkt")
(provide reset-globals! reset-todo! add-todo! inc-unions! set-global-σ!
         mk-imperative^-fixpoint
         prepare-imperative
         unions todo seen global-σ
         with-mutable-store
         with-mutable-worklist)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable global store and worklist.
(define unions #f)
(define todo #f)
(define seen #f)
(define global-σ #f)

(define (reset-globals! σ)
  (set! unions 0)
  (set! todo ∅)
  (set! seen (make-hash))
  (set! global-σ σ))
(define (inc-unions!) (set! unions (add1 unions)))
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

(define (join*-h! as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join-h! a vs)))

(define-syntax-rule (global-hash-getter σ* a)
  (hash-ref global-σ a (λ () (error 'global-hash-getter "Unbound address ~a" a))))

(define-syntax-rule (bind-join-h! (σ* jhσ a vs) body)
  (begin (join-h! a vs) body))
(define-syntax-rule (bind-join*-h! (σ* jh*σ as vss) body)
  (begin (join*-h! as vss) body))

(define-syntax-rule (mk-imperative^-fixpoint name ans^? ans^-v touches)
  (define (name step fst)
    (define clean-σ (restrict-to-reachable touches))
    (let loop ()
      (cond [(∅? todo) ;; → null?
             (define vs
               (for*/set ([(c at-unions) (in-hash seen)]
                          #:when (ans^? c))
                 (ans^-v c)))
             (values (format "State count: ~a" (hash-count seen))
                     (clean-σ global-σ vs)
                     vs)]
            [else
             (define todo-old todo)
             (reset-todo!)                        ;; → '()
             (for ([c (in-set todo-old)]) (step c)) ;; → in-list
             (loop)]))))

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