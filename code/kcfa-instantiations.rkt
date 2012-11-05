#lang racket
(require (rename-in racket/generator [yield real-yield]))
(require "kcfa.rkt" "data.rkt" "parse.rkt" 
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
#|
;; Compiled wide concrete store-passing set monad
(with-nonsparse
 (with-lazy
  (with-∞-ctx
         (with-whole-σ
          (with-narrow-set-monad
           (with-concrete
            (mk-analysis #:aval lazy-eval/c #:ans ans/c
                         #:σ-passing #:set-monad #:kcfa +inf.0
                         #:compiled)))))))
 (provide lazy-eval/c)

 (with-nonsparse
  (with-lazy
   (with-∞-ctx
          (with-whole-σ
           (with-narrow-set-monad
            (with-concrete
             (mk-analysis #:aval lazy-eval #:ans ans
                          #:σ-passing #:set-monad #:kcfa +inf.0)))))))
 (provide lazy-eval)

 (mk-special-set-fixpoint^ fix eval-set-fixpoint^ ans^?)
 (with-nonsparse
  (with-lazy
   (with-∞-ctx
          (with-whole-σ
           (with-σ-passing-set-monad
            (with-concrete
             (mk-analysis #:aval lazy-eval^/c #:ans ans^
                          #:fixpoint eval-set-fixpoint^
                          #:compiled #:set-monad #:wide #:σ-passing
                          #:kcfa +inf.0)))))))
 (provide lazy-eval^/c)
|#
(mk-special-set-fixpoint^ fix 0cfa-set-fixpoint^/c 0cfa-ans^/c?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c #:ans 0cfa-ans^/c
                   #:fixpoint 0cfa-set-fixpoint^/c
                   #:σ-passing
                   #:compiled #:wide #:set-monad)))))))
 (provide lazy-0cfa^/c)

(mk-set-fixpoint^ fix baseline-fixpoint baseline-ans?)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval baseline #:ans baseline-ans
                   #:fixpoint baseline-fixpoint
                   #:σ-passing #:wide #:set-monad)))))))
(provide baseline)

(mk-special-set-fixpoint^ fix 0cfa-set-fixpoint^ 0cfa-ans^?)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval 0cfa^ #:ans 0cfa-ans^
                   #:fixpoint 0cfa-set-fixpoint^
                   #:σ-passing #:wide #:set-monad)))))))
(provide 0cfa^)

(mk-special-set-fixpoint^ fix lazy-0cfa-set-fixpoint^ lazy-0cfa-ans^?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^ #:ans lazy-0cfa-ans^
                   #:fixpoint lazy-0cfa-set-fixpoint^
                   #:σ-passing #:wide #:set-monad)))))))
(provide lazy-0cfa^)

(mk-fix fix-filtered 0cfa-ans? 0cfa-ans-v)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-whole-σ
    (with-narrow-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa #:ans 0cfa-ans #:set-monad #:fixpoint fix-filtered
                   #:σ-passing)))))))
(provide lazy-0cfa)

(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-whole-σ
    (with-narrow-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa/c #:ans 0cfa-ans/c #:compiled
                   #:σ-passing
                   #:set-monad)))))))
(provide lazy-0cfa/c)

(mk-generator/wide/σ-∆s-fixpoint lazy-0cfa-gen^-fix gen-ans^?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-σ-∆s
            (with-σ-passing-generators
             (with-abstract
              (mk-analysis #:aval lazy-0cfa^-gen-σ-∆s #:ans gen-ans^
                           #:fixpoint lazy-0cfa-gen^-fix
                           #:σ-∆s
                           #:wide #:generators)))))))
(provide lazy-0cfa^-gen-σ-∆s)


(mk-∆-fix^ lazy-0cfa∆^-fixpoint 0cfa∆-ans^?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-σ-∆s
            (with-σ-passing-set-monad
             (with-abstract
              (mk-analysis #:aval lazy-0cfa∆/c #:ans 0cfa∆-ans^
                           #:fixpoint lazy-0cfa∆^-fixpoint
                           #:wide #:σ-∆s #:set-monad
                           #:compiled)))))))
(provide lazy-0cfa∆/c)


(mk-generator/wide/σ-∆s-fixpoint lazy-0cfa-σ-∆s-gen^-fix/c gen-ans^-σ-∆s/c?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-σ-∆s
            (with-σ-passing-generators
             (with-abstract
              (mk-analysis #:aval lazy-0cfa-gen-σ-∆s^/c #:ans gen-ans^-σ-∆s/c
                           #:fixpoint lazy-0cfa-σ-∆s-gen^-fix/c
                           #:σ-∆s
                           #:compiled #:wide #:generators)))))))
(provide lazy-0cfa-gen-σ-∆s^/c)

(mk-generator/wide/imperative-fixpoint lazy-0cfa-gen^-fix/c gen-ans^/c? gen-ans^/c-v global-gen-touches-0)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-mutable-store
    (with-global-σ-generators
     (with-abstract
      (mk-analysis #:aval lazy-0cfa-gen^/c #:ans gen-ans^/c
                   #:touches global-gen-touches-0
                   #:fixpoint lazy-0cfa-gen^-fix/c
                   #:compiled #:global-σ #:wide #:generators)))))))
(provide lazy-0cfa-gen^/c)

(mk-imperative^-fixpoint imperative-fixpoint/c imperative-ans/c? imperative-ans/c-v imperative-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-mutable-store
    (with-mutable-worklist
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c!
                   #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
                   #:ans imperative-ans/c
                   #:touches imperative-touches-0/c
                   #:fixpoint imperative-fixpoint/c
                   #:global-σ #:compiled #:wide)))))))
(provide lazy-0cfa^/c!)

(mk-prealloc^-fixpoint prealloc/imperative-fixpoint/c prealloc-ans/c? prealloc-ans/c-v prealloc-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-prealloc-store
    (with-mutable-worklist
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c/prealloc!
                   #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                   #:ans prealloc-ans/c
                   #:touches prealloc-touches-0/c
                   #:fixpoint prealloc/imperative-fixpoint/c
                   #:global-σ #:compiled #:wide)))))))
(provide lazy-0cfa^/c/prealloc!)

(mk-prealloc^-fixpoint prealloc/imperative-fixpoint prealloc-ans? prealloc-ans-v prealloc-touches-0)
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-prealloc-store
    (with-mutable-worklist
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^/prealloc!
                   #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                   #:ans prealloc-ans
                   #:touches prealloc-touches-0
                   #:fixpoint prealloc/imperative-fixpoint
                   #:global-σ #:wide)))))))
(provide lazy-0cfa^/prealloc!)
