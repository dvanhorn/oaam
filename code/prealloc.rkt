#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "data.rkt" "imperative.rkt" "context.rkt" "add-lib.rkt"
         "deltas.rkt")
(provide prepare-prealloc with-0-ctx/prealloc
         mk-prealloc/timestamp^-fixpoint
         mk-prealloc/∆s/acc^-fixpoint
         mk-prealloc/∆s^-fixpoint
         with-σ-∆s/acc/prealloc!
         with-σ-∆s/prealloc!
         grow-vector ;; helper
         global-vector-getter
         next-loc contour-table
         inc-next-loc!
         with-prealloc/timestamp-store)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable pre-allocated store
(define next-loc #f)
(define contour-table #f)

(define (inc-next-loc!) (set! next-loc (add1 next-loc)))

(define (grow-vector σ old-size)
  (for/vector #:length (* 2 old-size) #:fill ∅ ;; ∅ → '()
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

(define (prepare-prealloc parser sexp)
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
  (reset-globals! (make-vector (* 2 nlabels) ∅)) ;; ∅ → '()
  e*)

(define-syntax-rule (global-vector-getter σ* a)
  (vector-ref global-σ a))

(define-syntax-rule (with-0-ctx/prealloc body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [bind-rest (make-rename-transformer #'bind-rest-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0-prealloc)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(define (join! a vs)
  (define prev (vector-ref global-σ a))
  (define upd (⊓ vs prev))
  (unless (≡ prev upd)
    (vector-set! global-σ a upd)
    (inc-unions!)))

(define (join*! as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join! a vs)))

(define-syntax-rule (bind-join! (σ* j!σ a vs) body)
  (begin (join! a vs) body))
(define-syntax-rule (bind-join*! (σ* j*!σ as vss) body)
  (begin (join*! as vss) body))

(mk-mk-imperative/timestamp^-fixpoint
 mk-prealloc/timestamp^-fixpoint restrict-to-reachable/vector)

(define-syntax-rule (with-prealloc/timestamp-store body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join!)]
    [bind-join* (make-rename-transformer #'bind-join*!)]
    [getter (make-rename-transformer #'global-vector-getter)])
   body))

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
