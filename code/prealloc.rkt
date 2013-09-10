#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "data.rkt" "imperative.rkt" "context.rkt" "add-lib.rkt"
         "deltas.rkt")
(provide prepare-prealloc-base
         with-0-ctx/prealloc
         with-1-ctx/prealloc
         mk-prealloc/timestamp^-fixpoint
         mk-prealloc/timestamp^-fixpoint/stacked
         mk-prealloc/∆s/acc^-fixpoint
         mk-prealloc/∆s^-fixpoint
         with-σ-∆s/acc/prealloc!
         with-σ-∆s/prealloc!
         next-loc contour-table
         with-prealloc/timestamp-store
         with-prealloc/timestamp-store/stacked)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable pre-allocated store
(define next-loc #f)
(define contour-table #f)

(define (inc-next-loc!) (set! next-loc (add1 next-loc)))

(define (grow-vector σ old-size fill)
  (for/vector #:length (* 2 old-size) #:fill fill
                 ([v (in-vector σ)]
                  [i (in-naturals)]
                  #:when (< i old-size))
    v))
(define (ensure-σ-size fill)
  (and (= next-loc (vector-length global-σ))
       (set-global-σ! (grow-vector global-σ next-loc fill))))
(define (ensure-μ-size fill)
  (set-global-μ! (grow-vector global-μ next-loc fill)))

(define-simple-macro* (get-contour-index! c fill)
  (or (hash-ref contour-table c #f)
      (begin0 next-loc
              (and (ensure-σ-size fill)
                   #,@(if-μ #'(ensure-μ-size fill)))
              (hash-set! contour-table c next-loc)
              (inc-next-loc!))))

(define-syntax-rule (make-var-contour-0-prealloc x δ fill)
  (cond [(exact-nonnegative-integer? x) x]
        [else (get-contour-index! x fill)]))

(define-syntax-rule (make-var-contour-1-prealloc x δ fill)
  (get-contour-index! (cons x δ) fill))

(define (prepare-prealloc-base parser sexp fill μfill)
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
  (reset-globals! (make-vector (* 2 nlabels) fill)
                  (make-vector (* 2 nlabels) μfill))
  e*)

(mk-global-store-getter global-vector-getter global-σ vector-ref-ignore-third)
(mk-global-μ-getter global-vector-μgetter global-μ vector-ref-ignore-third)

(define-syntax-rule (with-0-ctx/prealloc fill body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [bind-rest (make-rename-transformer #'bind-rest-0)]
    [make-var-contour (syntax-rules () [(_ x y) (make-var-contour-0-prealloc x y fill)])])
   body))

(define-syntax-rule (with-1-ctx/prealloc fill body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-1)]
    [bind-rest (make-rename-transformer #'bind-rest-1)]
    [make-var-contour (syntax-rules () [(_ x y) (make-var-contour-1-prealloc x y fill)])])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(mk-mk-imperative/timestamp^-fixpoint
 mk-prealloc/timestamp^-fixpoint restrict-to-reachable/vector (void))

(mk-with-store with-prealloc/timestamp-store
               #:μbump mk-μbump vector-ref-ignore-third vector-set!
               #:join mk-joiner vector-ref-ignore-third vector-set!
               global-vector-getter
               global-vector-μgetter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lossless timestamp approximation
(mk-global-store-getter/stacked global-vector-getter/stacked global-σ vector-ref-ignore-third)
(mk-global-μ-getter/stacked global-vector-μgetter/stacked global-μ vector-ref-ignore-third)

(mk-with-store with-prealloc/timestamp-store/stacked
               #:μbump mk-μbump/stacked vector-ref-ignore-third vector-set!
               #:join mk-joiner/stacked vector-ref-ignore-third vector-set!
               global-vector-getter/stacked
               global-vector-μgetter/stacked)

(define-syntax-rule (restrict-to-reachable/vector/stacked touches)
  (let ()
    (define rtr (restrict-to-reachable touches))
    (λ (σ v)
       (rtr
        (for/hash ([stack (in-vector σ)]
                   [i (in-naturals)])
          (match stack
            [(cons (cons t vs) stack)
             (values i vs)]
            [_ (values i nothing)]))
        v))))

(mk-mk-imperative/timestamp^-fixpoint
 mk-prealloc/timestamp^-fixpoint/stacked restrict-to-reachable/vector/stacked (reset-∆?!))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accumulated deltas
(define-syntax-rule (vector-ref-ignore-third v a ignore) (vector-ref v a))

(define-syntax-rule (with-σ-∆s/acc/prealloc! body)
  (begin
    (mk-add-∆/s add-∆/acc/prealloc add-∆s/acc/prealloc bind-join/∆s/acc/prealloc bind-join*/∆s/acc/prealloc
             vector-ref-ignore-third)
   (with-σ-∆s/acc!
            (splicing-syntax-parameterize
             ([bind-join (make-rename-transformer #'bind-join/∆s/acc/prealloc)]
              [bind-join* (make-rename-transformer #'bind-join*/∆s/acc/prealloc)]
              [getter (make-rename-transformer #'global-vector-getter)]
              [μgetter (make-rename-transformer #'global-vector-μgetter)])
             body))))
(mk-mk-imperative/∆s/acc^-fixpoint
  mk-prealloc/∆s/acc^-fixpoint restrict-to-reachable/vector mk-joiner vector-ref-ignore-third vector-set! vector-set! vector-ref-ignore-third)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Imperative deltas

(define-syntax-rule (with-σ-∆s/prealloc! body)
  (begin
    (mk-add-∆/s! add-∆/prealloc!
             add-∆s/prealloc!
             bind-join/∆s/prealloc
             bind-join*/∆s/prealloc
             vector-ref-ignore-third)
    (with-σ-∆s!
             (splicing-syntax-parameterize
              ([bind-join (make-rename-transformer #'bind-join/∆s/prealloc)]
               [bind-join* (make-rename-transformer #'bind-join*/∆s/prealloc)]
               [getter (make-rename-transformer #'global-vector-getter)]
               [μgetter (make-rename-transformer #'global-vector-μgetter)])
              body))))
(mk-mk-imperative/∆s^-fixpoint
  mk-prealloc/∆s^-fixpoint restrict-to-reachable/vector mk-joiner vector-ref-ignore-third vector-set! vector-set! vector-ref-ignore-third)
