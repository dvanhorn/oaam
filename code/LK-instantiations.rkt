#lang racket
(require (rename-in racket/generator [yield real-yield]))
(require "LK.rkt" "data.rkt" "parse.rkt" 
         "primitives.rkt" "fix.rkt"
         ;; different components of instantiantiations
         "lazy-strict.rkt"
         "context.rkt"
         "deltas.rkt"
         "generators.rkt"
         "store-passing.rkt"
         "imperative.rkt"
         "prealloc.rkt"
         "nonsparse.rkt"
         racket/splicing)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete semantics

(define (eval-widen b)
  (cond [(atomic? b) b]
        [else (error "Unknown base value" b)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of common parameterizations

(define-syntax-rule (with-concrete body)
  (splicing-syntax-parameterize
   ([widen (make-rename-transformer #'eval-widen)])
   body))

(define-syntax-rule (with-abstract body)
  (splicing-syntax-parameterize
   ([widen (make-rename-transformer #'flatten-value)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators
;; "bl"
(mk-set-fixpoint^ fix baseline-fixpoint baseline-ans?)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval LK-baseline #:ans baseline-ans
                   #:fixpoint baseline-fixpoint
                   #:σ-passing #:wide #:set-monad)))))))
(provide LK-baseline)

;; "pd"
#;#;
(mk-prealloc/∆s^-fixpoint prealloc/∆s-fixpoint/c prealloc/∆s-ans/c?
              prealloc/∆s-ans/c-v prealloc/∆s-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-σ-∆s/prealloc!
    (with-abstract
      (mk-analysis #:aval LK-lazy-0cfa^/c/∆s/prealloc!
                   #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                   #:ans prealloc/∆s-ans/c
                   #:touches prealloc/∆s-touches-0/c
                   #:fixpoint prealloc/∆s-fixpoint/c
                   #:global-σ #:compiled #:wide))))))
(define LK-lazy-0cfa^/c/∆s/prealloc! values)
(provide LK-lazy-0cfa^/c/∆s/prealloc!)
