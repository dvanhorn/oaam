#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "data.rkt" "imperative.rkt" "context.rkt" "add-lib.rkt"
         "deltas.rkt")
(provide prepare-prealloc
         prepare-prealloc/stacked
         with-0-ctx/prealloc
         mk-prealloc/timestamp^-fixpoint
         mk-prealloc/timestamp^-fixpoint/stacked
         mk-prealloc/∆s/acc^-fixpoint
         mk-prealloc/∆s^-fixpoint
         with-σ-∆s/acc/prealloc!
         with-σ-∆s/prealloc!
         grow-vector ;; helper
         next-loc contour-table
         with-prealloc/timestamp-store
         with-prealloc/timestamp-store/stacked)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable pre-allocated store
(define next-loc #f)
(define contour-table #f)

(define nothing-proxy nothing)
(define (inc-next-loc!) (set! next-loc (add1 next-loc)))

(define (grow-vector σ old-size)
  (for/vector #:length (* 2 old-size) #:fill nothing-proxy ;; ∅ → '()
                 ([v (in-vector σ)]
                  [i (in-naturals)]
                  #:when (< i old-size))
    v))
(define (ensure-σ-size)
  (when (= next-loc (vector-length global-σ))
    (set-global-σ! (grow-vector global-σ next-loc))))

(define-syntax-rule (get-contour-index!-0 c)
  (or (hash-ref contour-table c #f)
      (begin0 next-loc
              (ensure-σ-size)
              (hash-set! contour-table c next-loc)
              (inc-next-loc!))))

(define-syntax-rule (make-var-contour-0-prealloc x δ)
  (cond [(exact-nonnegative-integer? x) x]
        [else (get-contour-index!-0 x)]))

(define (prepare-prealloc-base parser sexp)
  (define nlabels 0)
  (define (fresh-label!) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define (fresh-variable! x) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define-values (e renaming) (parser sexp fresh-label! fresh-variable!))
  (define e* (add-lib e renaming fresh-label! fresh-variable!))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (set! next-loc nlabels)
  (set! contour-table (make-hash))
  (reset-globals! (make-vector (* 2 nlabels) nothing-proxy))
  e*)
(define (prepare-prealloc parser sexp)
  (set! nothing-proxy nothing)
  (prepare-prealloc-base parser sexp))
(define (prepare-prealloc/stacked parser sexp)
  (set! nothing-proxy '())
  (prepare-prealloc-base parser sexp))

(mk-global-store-getter global-vector-getter vector-ref-ignore-third)

(define-syntax-rule (with-0-ctx/prealloc body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [bind-rest (make-rename-transformer #'bind-rest-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0-prealloc)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(mk-joiner join! vector-ref-ignore-third vector-set!)
(mk-join* join*! join!)
(mk-bind-joiner bind-join! join!)
(mk-bind-joiner bind-join*! join*!)

(mk-mk-imperative/timestamp^-fixpoint
 mk-prealloc/timestamp^-fixpoint restrict-to-reachable/vector (void))

(mk-with-store with-prealloc/timestamp-store
               bind-join!
               bind-join*!
               global-vector-getter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lossless timestamp approximation
(mk-global-store-getter/stacked global-vector-getter/stacked vector-ref-ignore-third)
(mk-joiner/stacked join/stacked! vector-ref-ignore-third vector-set!)
(mk-join* join*/stacked! join/stacked!)
(mk-bind-joiner bind-join/stacked! join/stacked!)
(mk-bind-joiner bind-join*/stacked! join*/stacked!)

(define (restrict-to-reachable/vector/stacked touches)
  (define rtr (restrict-to-reachable touches))
  (λ (σ v)
     (rtr
      (for/hash ([stack (in-vector σ)]
                 [i (in-naturals)])
        (match stack
          [(cons (cons t vs) stack)
           (values i vs)]
          [_ (values i ∅)]))
      v)))

(mk-mk-imperative/timestamp^-fixpoint
 mk-prealloc/timestamp^-fixpoint/stacked restrict-to-reachable/vector/stacked (reset-∆?!))

(mk-with-store with-prealloc/timestamp-store/stacked
               bind-join/stacked!
               bind-join*/stacked!
               global-vector-getter/stacked)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accumulated deltas
(define-syntax-rule (vector-ref-ignore-third v a ignore) (vector-ref v a))

(mk-add-∆/s add-∆/acc/prealloc add-∆s/acc/prealloc bind-join/∆s/acc/prealloc bind-join*/∆s/acc/prealloc
             vector-ref-ignore-third)

(define-syntax-rule (with-σ-∆s/acc/prealloc! body)
  (with-σ-∆s/acc!
   (splicing-syntax-parameterize
    ([bind-join (make-rename-transformer #'bind-join/∆s/acc/prealloc)]
     [bind-join* (make-rename-transformer #'bind-join*/∆s/acc/prealloc)]
     [getter (make-rename-transformer #'global-vector-getter)])
    body)))
(mk-mk-imperative/∆s/acc^-fixpoint
  mk-prealloc/∆s/acc^-fixpoint restrict-to-reachable/vector join! vector-set! vector-ref-ignore-third)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Imperative deltas
(mk-add-∆/s! add-∆/prealloc! add-∆s/prealloc! bind-join/∆s/prealloc bind-join*/∆s/prealloc
             vector-ref-ignore-third)

(define-syntax-rule (with-σ-∆s/prealloc! body)
  (with-σ-∆s!
   (splicing-syntax-parameterize
    ([bind-join (make-rename-transformer #'bind-join/∆s/prealloc)]
     [bind-join* (make-rename-transformer #'bind-join*/∆s/prealloc)]
     [getter (make-rename-transformer #'global-vector-getter)])
    body)))
(mk-mk-imperative/∆s^-fixpoint
  mk-prealloc/∆s^-fixpoint restrict-to-reachable/vector join! vector-set! vector-ref-ignore-third)
