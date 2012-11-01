#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "data.rkt")
(provide reset-globals! reset-todo! inc-unions! set-global-σ!
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

(define-for-syntax (yield! stx)
  (syntax-case stx ()
    [(_ e) #'(let ([c e])
               (unless (= unions (hash-ref seen c -1))
                 (hash-set! seen c unions)
                 (add-todo! c)))])) ;; ∪1 → cons

(define (join-h! a vs)
  (define prev (hash-ref global-σ a ∅))
  (define upd (⊓ vs prev))
  (define same? (= (set-count upd) (set-count prev)))
  (unless same?
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