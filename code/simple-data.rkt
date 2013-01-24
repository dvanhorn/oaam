#lang racket
(require "notation.rkt" "data.rkt" racket/splicing)
(provide with-simple-data)

;; A simple set-based implementation of the value lattice.

(define setnull (set '()))
(define (simple-≡ vs0 vs1)
  (= (set-count vs0) (set-count vs1)))

(define-syntax-rule (with-simple-data . body) 
  (splicing-syntax-parameterize
      ([nothing (make-rename-transformer #'∅)]
       [is-nothing? (make-rename-transformer #'∅?)]
       [singleton (make-rename-transformer #'set)]
       [abstract-values? (make-rename-transformer #'set?)]
       [⊓ (make-rename-transformer #'set-union)]
       [⊓1 (make-rename-transformer #'set-add)]
       [rem1 (make-rename-transformer #'set-remove)]
       [⊑? (make-rename-transformer #'subset?)]
       [≡ (make-rename-transformer #'simple-≡)]
       [in-abstract-values (make-rename-transformer #'in-set)]
       [snull (make-rename-transformer #'setnull)])
    . body))

#|
 (define (log-bad-reification addr value)
  (log-info "Multiple list reifications due to ~a: ~a" addr value))
 (define-syntax-rule (reify-list σ v)
  (do (σ) loop ([-v v]) #:values 1
    (match -v
      [(consv A D)
       (do (σ) ([ares #:get σ A]
                [dres #:get σ D])
         (define car (set-first ares)) ;; XXX: check a/dres for ∅?
         (define cdr (set-first dres))
         (unless (∅? (set-rest res)) (log-bad-reification A ares))
         (unless (∅? (set-rest dres)) (log-bad-reification D dres))
         (do-comp #:bind (rest)
                  (loop σ cdr)
                  (do-values (cons car rest))))]
      [_ (unless (null? -v) (log-info "Bad list for reification ~a" -v))
         (do-values -v)])))
|#
