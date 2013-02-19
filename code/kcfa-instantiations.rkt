#lang racket
(require (rename-in racket/generator [yield real-yield])
         racket/stxparam)
(require "kcfa.rkt" "data.rkt" "parse.rkt" "add-lib.rkt"
         "primitives.rkt" "fix.rkt" "env.rkt"
         "simple-data.rkt" "bitvector-data.rkt" "bitvector-data-with-intervals.rkt"
         ;; different components of instantiantiations
         "lazy-strict.rkt"
         "context.rkt"
         "deltas.rkt"
         "generators.rkt"
         "store-passing.rkt"
         "imperative.rkt"
         "prealloc.rkt"
         "nonsparse.rkt"
         "sparse-wide.rkt"
         "sparse-narrow.rkt"
         "cfa2.rkt"
         "pdcfa.rkt"
         "gammacfa.rkt"
         racket/splicing)
(provide debug-check)
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
#;#;
(with-bitvector-data/intervals
 (with-lazy
  (with-0-ctx
   (with-abstract
    (with-sparse (mk-analysis)
     (begin #;#;
      with-ΓCFA (mk-analysis) 
       (mk-analysis #:aval sp-lazy-0cfa/c                    
                    #:touches sp-lazy-0cfa/c-touches
                    #:wide)))))))
(provide sp-lazy-0cfa/c)

(mk-sparse^-fixpoint
 sp-lazy-0cfa^/c-fix
 sp-lazy-0cfa^/c-ans? sp-lazy-0cfa^/c-ans-v
 sp-lazy-0cfa^/c-touches)
(with-bitvector-data
 (with-sparse^
  (with-lazy
   (with-0-ctx/prealloc/sparse
    (with-sparse-mutable-worklist
     (with-abstract
      (with-prepare-sparse-wide/prealloc (prepare-sparse-wide/prealloc)
       (mk-analysis #:aval sp-lazy-0cfa^/c
                    #:prepare (λ (sexp) (prepare-sparse-wide/prealloc parse-prog sexp))
                    #:ans  sp-lazy-0cfa^/c-ans
                    #:touches sp-lazy-0cfa^/c-touches
                    #:fixpoint sp-lazy-0cfa^/c-fix
                    #:global-σ 
                    #;
                    #:compiled #:wide))))))))
(provide sp-lazy-0cfa^/c)

#|
 (mk-sparse^-fixpoint
                sp-lazy-0cfa^/c-fix
                sp-lazy-0cfa^/c-ans? sp-lazy-0cfa^/c-ans-v
                sp-lazy-0cfa^/c-touches)
 (with-sparse^
 (with-lazy
  (with-0-ctx/prealloc/sparse
   (with-sparse-mutable-worklist
    (with-abstract
     (begin #;
     (begin-for-syntax (printf "Grr ~a~%" (syntax->datum ((syntax-parameter-value #'yield) #'(yield blah)))))
      (mk-analysis #:aval sp-lazy-0cfa^/c
                   #:prepare (λ (sexp) (prepare-sparse-wide/prealloc parse-prog sexp))
                   #:ans  sp-lazy-0cfa^/c-ans
                   #:touches sp-lazy-0cfa^/c-touches
                   #:fixpoint sp-lazy-0cfa^/c-fix
                   #:global-σ 
                   #:compiled #:wide)))))))
 (provide sp-lazy-0cfa^/c)

;; "pt2"
(mk-imperative/timestamp^-fixpoint 2prealloc/imperative-fixpoint/c 2prealloc-ans/c?
                                 2prealloc-ans/c-v 2prealloc-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-prealloc/timestamp-store
    (with-mutable-worklist
     (with-abstract
      (with-cfa2^ (mk-analysis)
        (mk-analysis #:aval lazy-cfa2^/c/prealloc/timestamp!
                     #:prepare (λ (sexp) (prepare-cfa2^ parse-prog sexp))
                     #:ans 2prealloc-ans/c
                     #:touches 2prealloc-touches-0/c
                     #:fixpoint 2prealloc/imperative-fixpoint/c
                     #:global-σ #;
                     #:compiled #:wide #:pushdown))))))))
(provide lazy-cfa2^/c/prealloc/timestamp!)

;; n0cfa
(mk-fix lazy-0CFA/c-fixpoint ln0-ans? ln0-ans-v)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-narrow-σ-passing
    (with-whole-σ
     (with-set-monad
      (with-abstract
       (mk-analysis #:aval lazy-0CFA/c #:ans ln0-ans
                    #:fixpoint lazy-0CFA/c-fixpoint
                    #:compiled))))))))
(provide lazy-0CFA/c)

(mk-imperative-narrow-fix lazy-ΓCFA/c-fixpoint lg0-ans? lg0-ans-v lg0-state-rσ lg0-touches)
;; g0cfa
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-narrow-σ-passing
    (with-whole-σ
     (with-narrow-mutable-worklist
      (with-abstract
       (with-ΓCFA (mk-analysis)
        (mk-analysis #:aval lazy-ΓCFA/c #:ans lg0-ans #:touches lg0-touches
                     #:state lg0-state
                     #:prepare (λ (sexp) (prepare-imperative-todo parse-prog sexp))
                     #:fixpoint lazy-ΓCFA/c-fixpoint
                     #:compiled)))))))))
(provide lazy-ΓCFA/c)

;; "pts"
(mk-imperative/timestamp^-fixpoint sprealloc/imperative-fixpoint/c sprealloc-ans/c?
                                 sprealloc-ans/c-v sprealloc-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-prealloc/timestamp-store
    (with-mutable-worklist
     (with-abstract
      (with-pdcfa^ (mk-analysis)
        (mk-analysis #:aval lazy-pdcfa^/c/prealloc/timestamp!
                     #:prepare (λ (sexp) (prepare-pdcfa^ parse-prog sexp))
                     #:ans sprealloc-ans/c
                     #:touches sprealloc-touches-0/c
                     #:fixpoint sprealloc/imperative-fixpoint/c
                     #:global-σ #:compiled #:wide #:pushdown))))))))
(provide lazy-pdcfa^/c/prealloc/timestamp!)

|#

#|
 ;; "sid"
 (mk-imperative/∆s^-fixpoint
                 s-imperative/∆s-fixpoint/c s-imperative/∆s-ans/c?
                 s-imperative/∆s-ans/c-v s-imperative/∆s-touches-0/c)
 (with-nonsparse
  (with-strict
   (with-0-ctx
    (with-σ-∆s!
     (with-abstract
       (mk-analysis #:aval 0cfa^/c/∆s!
                    #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
                    #:ans s-imperative/∆s-ans/c
                    #:touches s-imperative/∆s-touches-0/c
                    #:fixpoint s-imperative/∆s-fixpoint/c
                    #:global-σ #:compiled #:wide))))))
 (provide 0cfa^/c/∆s!)
 
 ;; "spd"
 (mk-prealloc/∆s^-fixpoint s-prealloc/∆s-fixpoint/c s-prealloc/∆s-ans/c?
               s-prealloc/∆s-ans/c-v s-prealloc/∆s-touches-0/c)
 (with-nonsparse
  (with-strict
   (with-0-ctx/prealloc
    (with-σ-∆s/prealloc!
     (with-abstract
       (mk-analysis #:aval 0cfa^/c/∆s/prealloc!
                    #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                    #:ans s-prealloc/∆s-ans/c
                    #:touches s-prealloc/∆s-touches-0/c
                    #:fixpoint s-prealloc/∆s-fixpoint/c
                    #:global-σ #:compiled #:wide))))))
 (provide 0cfa^/c/∆s/prealloc!)
 
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
       (mk-analysis #:aval baseline #:ans baseline-ans
                    #:fixpoint baseline-fixpoint
                    #:σ-passing #:wide #:set-monad)))))))
 (provide baseline)
 ;; "sp"
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
 ;; "ls"
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
 ;; "lc"
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
 ;; "ld"
 (mk-∆-fix^ lazy-0cfa∆^-fixpoint 0cfa∆-ans^?)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-σ-∆s
             (with-σ-passing-set-monad
              (with-abstract
               (mk-analysis #:aval lazy-0cfa^/c/∆s #:ans 0cfa∆-ans^
                            #:fixpoint lazy-0cfa∆^-fixpoint
                            #:wide #:σ-∆s #:set-monad
                            #:compiled)))))))
 (provide lazy-0cfa^/c/∆s) 
 
 ;; "fd"
 (mk-timestamp-∆-fix^ lazy-0cfa∆^-fixpoint/t lazy-0cfa∆/t-ans^?)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-σ-∆s
             (with-σ-passing-set-monad
              (with-abstract
               (mk-analysis #:aval lazy-0cfa^/c/∆s/t #:ans lazy-0cfa∆/t-ans^
                            #:fixpoint lazy-0cfa∆^-fixpoint/t
                            #:wide #:σ-∆s #:set-monad
                            #:compiled)))))))
 (provide lazy-0cfa^/c/∆s/t)
 
 ;; "ia"
 (mk-imperative/∆s/acc^-fixpoint
                 imperative/∆s/acc-fixpoint/c imperative/∆s/acc-ans/c?
                 imperative/∆s/acc-ans/c-v imperative/∆s/acc-touches-0/c)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-σ-∆s/acc!
     (with-abstract
       (mk-analysis #:aval lazy-0cfa^/c/∆s/acc!
                    #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
                    #:ans imperative/∆s/acc-ans/c
                    #:touches imperative/∆s/acc-touches-0/c
                    #:fixpoint imperative/∆s/acc-fixpoint/c
                    #:σ-∆s
                    #:global-σ #:compiled #:wide))))))
 (provide lazy-0cfa^/c/∆s/acc!)
 ;; "id"
 (mk-imperative/∆s^-fixpoint
                 imperative/∆s-fixpoint/c imperative/∆s-ans/c?
                 imperative/∆s-ans/c-v imperative/∆s-touches-0/c)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-σ-∆s!
     (with-abstract
       (mk-analysis #:aval lazy-0cfa^/c/∆s!
                    #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
                    #:ans imperative/∆s-ans/c
                    #:touches imperative/∆s-touches-0/c
                    #:fixpoint imperative/∆s-fixpoint/c
                    #:global-σ #:compiled #:wide))))))
 (provide lazy-0cfa^/c/∆s!)
 ;; "pa"
 (mk-prealloc/∆s/acc^-fixpoint prealloc/∆s/acc-fixpoint/c prealloc/∆s/acc-ans/c? 
               prealloc/∆s/acc-ans/c-v prealloc/∆s/acc-touches-0/c)
 (with-nonsparse
  (with-lazy
   (with-0-ctx/prealloc
    (with-σ-∆s/acc/prealloc!
     (with-abstract
       (mk-analysis #:aval lazy-0cfa^/c/∆s/acc/prealloc!
                    #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                    #:ans prealloc/∆s/acc-ans/c
                    #:touches prealloc/∆s/acc-touches-0/c
                    #:fixpoint prealloc/∆s/acc-fixpoint/c
                    #:σ-∆s
                    #:global-σ #:compiled #:wide))))))
 (provide lazy-0cfa^/c/∆s/acc/prealloc!)

|#
#;#;#;
;; "pd"
(mk-prealloc/∆s^-fixpoint prealloc/∆s-fixpoint/c prealloc/∆s-ans/c?
              prealloc/∆s-ans/c-v prealloc/∆s-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-σ-∆s/prealloc!
    (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c/∆s/prealloc!
                   #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                   #:ans prealloc/∆s-ans/c
                   #:touches prealloc/∆s-touches-0/c
                   #:fixpoint prealloc/∆s-fixpoint/c
                   #:global-σ #:compiled #:wide))))))
(provide lazy-0cfa^/c/∆s/prealloc!)

#|

;; "it"
(mk-imperative/timestamp^-fixpoint imperative-fixpoint/c imperative-ans/c?
                                   imperative-ans/c-v imperative-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-mutable-store
    (with-mutable-worklist
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c/timestamp!
                   #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
                   #:ans imperative-ans/c
                   #:touches imperative-touches-0/c
                   #:fixpoint imperative-fixpoint/c
                   #:global-σ #:compiled #:wide)))))))
(provide lazy-0cfa^/c/timestamp!)
|#
#;#;
;; "pt"
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-simple-data (clos: rlos: kont?)
     (mk-prealloc/timestamp^-fixpoint prealloc/imperative-fixpoint/c prealloc-ans/c?
                                      prealloc-joiner
                                      prealloc-ans/c-v prealloc-touches-0/c)
     (with-prealloc/timestamp-store (prealloc-joiner)
     (with-mutable-worklist
      (with-abstract
       (mk-analysis #:aval lazy-0cfa^/c/prealloc/timestamp!
                    #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                    #:ans prealloc-ans/c
                    #:touches prealloc-touches-0/c
                    #:fixpoint prealloc/imperative-fixpoint/c
                    #:global-σ #:compiled #:wide
                    #:clos clos #:rlos rlos #:kont kont?))))))))
(provide lazy-0cfa^/c/prealloc/timestamp!)

#|
 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; Evaluators for CM-extended Scheme
 (mk-set-fixpoint^ fix baseline/cm-fixpoint baseline/cm-ans?)
 (with-nonsparse
   (with-strict
   (with-0-ctx
    (with-whole-σ
     (with-σ-passing-set-monad
      (with-abstract
       (mk-analysis #:aval baseline/cm #:ans baseline/cm-ans
                    #:fixpoint baseline/cm-fixpoint
                    #:CM (set 'A 'S)
                    #:σ-passing #:wide #:set-monad)))))))
 (provide baseline/cm)

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluators not in the paper
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instantiations not in the paper
#|
 (mk-prealloc/timestamp^-fixpoint prealloc/imperative-fixpoint prealloc-ans? prealloc-ans-v prealloc-touches-0)
 (with-nonsparse
  (with-lazy
   (with-0-ctx/prealloc
    (with-prealloc/timestamp-store
     (with-mutable-worklist
      (with-abstract
       (mk-analysis #:aval lazy-0cfa^/prealloc/timestamp!
                    #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
                    #:ans prealloc-ans
                    #:touches prealloc-touches-0
                    #:fixpoint prealloc/imperative-fixpoint
                    #:global-σ #:wide)))))))
 (provide lazy-0cfa^/prealloc/timestamp!)

 (mk-timestamp-∆-fix^ lazy-0cfa∆^-timestamp-fixpoint 0cfa∆-timestamp-ans^?)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-σ-∆s
             (with-σ-passing-set-monad
              (with-abstract
               (mk-analysis #:aval lazy-0cfa∆/c/timestamp #:ans 0cfa∆-timestamp-ans^
                            #:fixpoint lazy-0cfa∆^-timestamp-fixpoint
                            #:wide #:σ-∆s #:set-monad
                            #:compiled)))))))
 (provide lazy-0cfa∆/c/timestamp) 
 
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
 
 (mk-generator/wide/σ-∆s-fixpoint lazy-0cfa-gen^-fix gen-ans^? gen-touches-0)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-σ-∆s
             (with-σ-passing-generators
              (with-abstract
               (mk-analysis #:aval lazy-0cfa-gen-σ-∆s^ #:ans gen-ans^
                            #:fixpoint lazy-0cfa-gen^-fix
                            #:touches gen-touches-0
                            #:σ-∆s
                            #:wide #:generators)))))))
 (provide lazy-0cfa-gen-σ-∆s^)
 
 (mk-generator/wide/σ-∆s-fixpoint lazy-0cfa-σ-∆s-gen^-fix/c gen-ans^-σ-∆s/c? gen-touches-0/c)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-σ-∆s
             (with-σ-passing-generators
              (with-abstract
               (mk-analysis #:aval lazy-0cfa-gen-σ-∆s^/c #:ans gen-ans^-σ-∆s/c
                            #:touches gen-touches-0/c
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
|#
