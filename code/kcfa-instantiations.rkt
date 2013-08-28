#lang racket
(require (rename-in racket/generator [yield real-yield]))
(require "kcfa.rkt" "data.rkt" "parse.rkt" 
         "primitives.rkt" "fix.rkt" "do.rkt"
         ;; different components of instantiantiations
         "lazy-strict.rkt"
         "context.rkt"
         "deltas.rkt"
         "generators.rkt"
         "store-passing.rkt"
         "regular-pushdown.rkt"
         "imperative.rkt"
         "prealloc.rkt"
         "nonsparse.rkt"
         "graph.rkt"
         racket/splicing)

#|

Notes wrt. use:

running baseline analysis on file

Welcome to Racket v5.3.3.
-> (require "kcfa-instantiations.rkt")
-> (define (sch->sexp file)
  (with-input-from-file file
    (λ () (for/list ([form (in-port read)]) form))))
-> (require "handle-limits.rkt")
-> (define-values (state-count-msg point-count-msg heap anss)
   (with-limit-handler (baseline (sch->sexp "../benchmarks/church.sch"))))
-> state-count-msg
"State count: 7140"
-> point-count-msg
"Point count: 893"
-> heap #;(it's usually pretty long)
;; => hash[symbol -> set[val]]
;;    where val is one of
;;    - value-node?
-> anss
;; => set[ans-container]

|#

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

(define-syntax-rule (with-abstract . body)
  (splicing-syntax-parameterize
   ([widen (make-rename-transformer #'flatten-value)])
   . body))

#;#;#;
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

#;#;#;
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

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; Potpourris of evaluators
;; ;; "bl"
;; (mk-set-fixpoint^ fix baseline-fixpoint baseline-ans?)
;; (with-nonsparse
;;  (with-strict
;;   (with-0-ctx
;;    (with-whole-σ
;;     (with-σ-passing-set-monad
;;      (with-abstract
;;       (mk-analysis #:aval baseline #:ans baseline-ans
;;                    #:fixpoint baseline-fixpoint
;;                    #:σ-passing #:wide #:set-monad)))))))
;; (provide baseline)

#;#;#;
;; "spt"
(mk-special-set-fixpoint^ fix 0cfa-set-fixpoint^/t 0cfa-ans^/t?)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval 0cfa^/t #:ans 0cfa-ans^/t
                   #:fixpoint 0cfa-set-fixpoint^/t
                   #:σ-passing #:wide #:set-monad)))))))
(provide 0cfa^/t)

#;#;#;
;; The baseline in the paper
;; "sp"
(mk-special2-set-fixpoint^ fix 0cfa-set-fixpoint^ 0cfa-ans^ 0ev^ 0co^ #f)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval 0cfa^ #:ans 0cfa-ans^
                   #:fixpoint 0cfa-set-fixpoint^
                   #:σ-passing #:wide #:set-monad
                   #:ev 0ev^ #:co 0co^)))))))
(provide 0cfa^)

#;#;#;
;; timestamp strict deltas
;; "sdt"
(mk-∆-fix^ 0cfa-∆s-fixpoint^/t 0cfa-∆s-ans^/t?)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-σ-∆s
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval 0cfa^-∆s/t #:ans 0cfa-∆s-ans^/t
                   #:fixpoint 0cfa-∆s-fixpoint^/t
                   #:σ-passing #:σ-∆s #:wide #:set-monad)))))))
(provide 0cfa^-∆s/t)

#;#;#;
;; "ls"
(mk-special2-set-fixpoint^ fix lazy-0cfa-set-fixpoint^ lazy-0cfa-ans^ l-0ev l-0co #f)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^ #:ans lazy-0cfa-ans^
                   #:fixpoint lazy-0cfa-set-fixpoint^
                   #:σ-passing #:wide #:set-monad
                   #:ev l-0ev #:co l-0co)))))))
(provide lazy-0cfa^)

#;#;#;
;; "lst"
(mk-∆-fix^ lazy-0cfa-∆s-fixpoint^/t lazy-0cfa-∆s-ans^/t?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-σ-∆s
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^-∆s/t #:ans lazy-0cfa-∆s-ans^/t
                   #:fixpoint lazy-0cfa-∆s-fixpoint^/t
                   #:σ-passing #:σ-∆s #:wide #:set-monad)))))))
(provide lazy-0cfa^-∆s/t)

#;
;; "lc"
(splicing-syntax-parameterize ([generate-graph? #t])
 (mk-special2-set-fixpoint^ fix 0cfa-set-fixpoint^/c 0cfa-ans^/c levc lcoc #t)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-whole-σ
     (with-σ-passing-set-monad
      (with-abstract
       (mk-analysis #:aval lazy-0cfa^/c #:ans 0cfa-ans^/c
                    #:fixpoint 0cfa-set-fixpoint^/c
                    #:σ-passing
                    #:compiled #:wide #:set-monad
                    #:ev levc #:co lcoc))))))))
#; (provide lazy-0cfa^/c)

#;#;#;
;; "lct"
(mk-∆-fix^ lazy-0cfa-∆s-fixpoint^/t/c lazy-0cfa-∆s-ans^/t/c?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-σ-∆s
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^-∆s/t/c #:ans lazy-0cfa-∆s-ans^/t/c
                   #:fixpoint lazy-0cfa-∆s-fixpoint^/t/c
                   #:σ-passing #:wide #:σ-∆s #:set-monad #:compiled)))))))
(provide lazy-0cfa^-∆s/t/c)

#;#;#;
;; "ld"
(mk-∆-fix2^ lazy-0cfa∆^-fixpoint 0cfa∆-ans^?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-σ-∆s
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c/∆s #:ans 0cfa∆-ans^
                   #:fixpoint lazy-0cfa∆^-fixpoint
                   #:wide #:σ-∆s #:set-monad #:σ-passing
                   #:compiled)))))))
(provide lazy-0cfa^/c/∆s)

;; ;; "fd"
;; (mk-timestamp-∆-fix^ lazy-0cfa∆^-fixpoint/t lazy-0cfa∆/t-ans^?)
;; (with-nonsparse
;;  (with-lazy
;;   (with-0-ctx
;;    (with-σ-∆s
;;             (with-σ-passing-set-monad
;;              (with-abstract
;;               (mk-analysis #:aval lazy-0cfa^/c/∆s/t #:ans lazy-0cfa∆/t-ans^
;;                            #:fixpoint lazy-0cfa∆^-fixpoint/t
;;                            #:wide #:σ-∆s #:set-monad
;;                            #:compiled)))))))
;; (provide lazy-0cfa^/c/∆s/t)

;; ;; "ia"
;; (mk-imperative/∆s/acc^-fixpoint
;;                 imperative/∆s/acc-fixpoint/c imperative/∆s/acc-ans/c?
;;                 imperative/∆s/acc-ans/c-v imperative/∆s/acc-touches-0/c)
;; (with-nonsparse
;;  (with-lazy
;;   (with-0-ctx
;;    (with-σ-∆s/acc!
;;     (with-abstract
;;       (mk-analysis #:aval lazy-0cfa^/c/∆s/acc!
;;                    #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
;;                    #:ans imperative/∆s/acc-ans/c
;;                    #:touches imperative/∆s/acc-touches-0/c
;;                    #:fixpoint imperative/∆s/acc-fixpoint/c
;;                    #:σ-∆s
;;                    #:global-σ #:compiled #:wide))))))
;; (provide lazy-0cfa^/c/∆s/acc!)
;; ;; "id"
;; (mk-imperative/∆s^-fixpoint
;;                 imperative/∆s-fixpoint/c imperative/∆s-ans/c?
;;                 imperative/∆s-ans/c-v imperative/∆s-touches-0/c)
;; (with-nonsparse
;;  (with-lazy
;;   (with-0-ctx
;;    (with-σ-∆s!
;;     (with-abstract
;;       (mk-analysis #:aval lazy-0cfa^/c/∆s!
;;                    #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
;;                    #:ans imperative/∆s-ans/c
;;                    #:touches imperative/∆s-touches-0/c
;;                    #:fixpoint imperative/∆s-fixpoint/c
;;                    #:global-σ #:compiled #:wide))))))
;; (provide lazy-0cfa^/c/∆s!)
;; ;; "is"
;; (mk-imperative/timestamp^-fixpoint/stacked
;;                 imperative/∆s-fixpoint/stacked/c imperative/∆s-ans/stacked/c?
;;                 imperative/∆s-ans/stacked/c-v imperative/∆s-touches-0/stacked/c)
;; (with-nonsparse
;;  (with-lazy
;;   (with-0-ctx
;;    (with-mutable-store/stacked
;;     (with-mutable-worklist/stacked^
;;     (with-abstract
;;       (mk-analysis #:aval lazy-0cfa^/c/∆s/stacked!
;;                    #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
;;                    #:ans imperative/∆s-ans/stacked/c
;;                    #:touches imperative/∆s-touches-0/stacked/c
;;                    #:fixpoint imperative/∆s-fixpoint/stacked/c
;;                    #:global-σ #:compiled #:wide)))))))
;; (provide lazy-0cfa^/c/∆s/stacked!)
;; ;; "pa"
;; (mk-prealloc/∆s/acc^-fixpoint prealloc/∆s/acc-fixpoint/c prealloc/∆s/acc-ans/c? 
;;               prealloc/∆s/acc-ans/c-v prealloc/∆s/acc-touches-0/c)
;; (with-nonsparse
;;  (with-lazy
;;   (with-0-ctx/prealloc
;;    (with-σ-∆s/acc/prealloc!
;;     (with-abstract
;;       (mk-analysis #:aval lazy-0cfa^/c/∆s/acc/prealloc!
;;                    #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
;;                    #:ans prealloc/∆s/acc-ans/c
;;                    #:touches prealloc/∆s/acc-touches-0/c
;;                    #:fixpoint prealloc/∆s/acc-fixpoint/c
;;                    #:σ-∆s
;;                    #:global-σ #:compiled #:wide))))))
;; (provide lazy-0cfa^/c/∆s/acc/prealloc!)
;; ;; "pd"
;; (mk-prealloc/∆s^-fixpoint prealloc/∆s-fixpoint/c prealloc/∆s-ans/c?
;;               prealloc/∆s-ans/c-v prealloc/∆s-touches-0/c)
;; (with-nonsparse
;;  (with-lazy
;;   (with-0-ctx/prealloc
;;    (with-σ-∆s/prealloc!
;;     (with-abstract
;;      (define pd-e (box #f))
;;       (mk-analysis #:aval lazy-0cfa^/c/∆s/prealloc!
;;                    #:prepare (λ (sexp)
;;                                 (define e* (prepare-prealloc parse-prog sexp))
;;                                 (set-box! pd-e e*)
;;                                 e*)
;;                    #:ans prealloc/∆s-ans/c
;;                    #:touches prealloc/∆s-touches-0/c
;;                    #:fixpoint prealloc/∆s-fixpoint/c
;;                    #:global-σ #:compiled #:wide))))))
;; (provide lazy-0cfa^/c/∆s/prealloc!)


;; "ps"
#;#;
(splicing-syntax-parameterize ([generate-graph? #f]
                               [abs-count? #t]
                               [global-σ? #t])
 (mk-prealloc/timestamp^-fixpoint/stacked
  prealloc/∆s-fixpoint/stacked/c
  prealloc/∆s-state-base/stacked/c
  prealloc/∆s-point/stacked/c
  prealloc/∆s-ans/stacked/c
  prealloc/∆s-touches-0/stacked/c
  #:ev psev
  #:co psco #:compiled)
 (with-nonsparse
  (with-regular
   (with-lazy
    (with-0-ctx/prealloc
     (with-prealloc/timestamp-store/stacked
      (with-mutable-worklist/stacked^
       (with-abstract
        (define ps-e (box #f))
        (mk-analysis #:aval lazy-0cfa^/c/∆s/prealloc/stacked!
                     #:prepare (λ (sexp)
                                  (define e* (prepare-prealloc/stacked parse-prog sexp))
                                  (set-box! ps-e e*)
                                  e*)
                     #:state-base prealloc/∆s-state-base/stacked/c
                     #:point prealloc/∆s-point/stacked/c
                     #:ans prealloc/∆s-ans/stacked/c
                     #:touches prealloc/∆s-touches-0/stacked/c
                     #:fixpoint prealloc/∆s-fixpoint/stacked/c
                     #:co psco #:compiled ;#:ev psev
                     #:global-σ #:wide)))))))))
(provide lazy-0cfa^/c/∆s/prealloc/stacked!)

;; "lcg"
(splicing-syntax-parameterize ([generate-graph? #f]
                               [abs-count? #t]
                               [compiled? #t])
 (with-whole-GH-σ #;with-σ-∆s
  (with-timestamp-∆-fix/Γ
    [lcgsb
     lcgpnt
     (lcgco lcgdr lcgchk lcgans lcgap lcgcc lcgev)
     lcgtouches
     lcgroot
     #:narrow]
   (with-nonsparse
    (;with-regular
     with-pushdown #:rtk lcgrtk #:kont lcgkont #:co lcgco #:ctx lcgctx #:root lcgroot #:touches lcgtouches #:state-base lcgsb #:point lcgpnt #:narrow
     (with-lazy
      (with-0-ctx
       (with-abstract
        (mk-analysis #:aval lazy-0cfa/c/Γ/μ/∆s
                     #:state-base lcgsb
                     #:point lcgpnt
                     #:touches lcgtouches
                     #:root lcgroot
                     #:co lcgco #:dr lcgdr #:chk lcgchk #:ans lcgans #:ap lcgap #:cc lcgcc #:ev lcgev
                     #:rtk lcgrtk #:kont lcgkont #:ctx lcgctx
                     #:σ-passing)))))))))
(provide lazy-0cfa/c/Γ/μ/∆s)

#;#;#;
;; "ps1"
(mk-prealloc/timestamp^-fixpoint/stacked prealloc/∆s-fixpoint-1/stacked/c prealloc/∆s-ans-1/stacked/c prealloc/∆s-touches-1/stacked/c)
(with-nonsparse
 (with-lazy
  (with-1-ctx/prealloc
   (with-prealloc/timestamp-store/stacked
    (with-mutable-worklist/stacked^
    (with-abstract
     (define ps-e-1 (box #f))
      (mk-analysis #:aval lazy-1cfa^/c/∆s/prealloc/stacked!
                   #:prepare (λ (sexp)
                                (define e* (prepare-prealloc/stacked parse-prog sexp))
                                (set-box! ps-e-1 e*)
                                e*)
                   #:ans prealloc/∆s-ans-1/stacked/c
                   #:touches prealloc/∆s-touches-1/stacked/c
                   #:fixpoint prealloc/∆s-fixpoint-1/stacked/c
                   #:kcfa 1
                   #:global-σ #:compiled #:wide)))))))
(provide lazy-1cfa^/c/∆s/prealloc/stacked!)
;; ;; "it"
;; (mk-imperative/timestamp^-fixpoint imperative-fixpoint/c imperative-ans/c?
;;                                    imperative-ans/c-v imperative-touches-0/c)
;; (wioth-nonsparse
;;  (with-lazy
;;   (with-0-ctx
;;    (with-mutable-store
;;     (with-mutable-worklist^
;;      (with-abstract
;;       (mk-analysis #:aval lazy-0cfa^/c/timestamp!
;;                    #:prepare (λ (sexp) (prepare-imperative parse-prog sexp))
;;                    #:ans imperative-ans/c
;;                    #:touches imperative-touches-0/c
;;                    #:fixpoint imperative-fixpoint/c
;;                    #:global-σ #:compiled #:wide)))))))
;; (provide lazy-0cfa^/c/timestamp!)
;; ;; "pt"
;; (mk-prealloc/timestamp^-fixpoint prealloc/imperative-fixpoint/c prealloc-ans/c?
;;                                  prealloc-ans/c-v prealloc-touches-0/c)
;; (with-nonsparse
;;  (with-lazy
;;   (with-0-ctx/prealloc
;;    (with-prealloc/timestamp-store
;;     (with-mutable-worklist^
;;      (with-abstract
;;       (mk-analysis #:aval lazy-0cfa^/c/prealloc/timestamp!
;;                    #:prepare (λ (sexp) (prepare-prealloc parse-prog sexp))
;;                    #:ans prealloc-ans/c
;;                    #:touches prealloc-touches-0/c
;;                    #:fixpoint prealloc/imperative-fixpoint/c
;;                    #:global-σ #:compiled #:wide)))))))
;; (provide lazy-0cfa^/c/prealloc/timestamp!)

#;#;#;
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
     (with-mutable-worklist^
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
 
 (mk-special2-set-fixpoint^ fix lazy-0cfa-set-fixpoint^2 lazy-0cfa-ans^ #f)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-whole-σ
     (with-σ-passing-set-monad
      (with-abstract
       (mk-analysis #:aval lazy-0cfa^2 #:ans lazy-0cfa-ans^2
                    #:fixpoint lazy-0cfa-set-fixpoint^2
                    #:σ-passing #:wide #:set-monad)))))))
 (provide lazy-0cfa^2)
 
 (mk-special3-set-fixpoint^ fix lazy-0cfa-set-fixpoint^3 lazy-0cfa-ans^3?)
 (with-nonsparse
  (with-lazy
   (with-0-ctx
    (with-whole-σ
     (with-σ-passing-set-monad
      (with-abstract
       (mk-analysis #:aval lazy-0cfa^3 #:ans lazy-0cfa-ans^3
                    #:fixpoint lazy-0cfa-set-fixpoint^3
                    #:σ-passing #:wide #:set-monad)))))))
 (provide lazy-0cfa^3)
 
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
