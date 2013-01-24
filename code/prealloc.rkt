#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "parameters.rkt"
         "data.rkt" "imperative.rkt" "context.rkt" "add-lib.rkt"
         "deltas.rkt")
(provide prepare-prealloc with-0-ctx/prealloc
         mk-prealloc/timestamp^-fixpoint
         mk-prealloc/∆s/acc^-fixpoint
         mk-prealloc/∆s^-fixpoint
         with-σ-∆s/acc/prealloc!
         with-σ-∆s/prealloc!
         global-vector-getter
         next-loc contour-table
         inc-next-loc!
         with-prealloc/timestamp-store)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable pre-allocated store
(define next-loc #f)
(define contour-table #f)

(define (inc-next-loc!) (set! next-loc (add1/debug next-loc 'inc-next-loc!)))

(define (prepare-prealloc parser sexp)
  (define nlabels 0)
  (define (fresh-label! ctx new?) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define (fresh-variable! x ctx) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define-values (e renaming ps) (parser sexp fresh-label! fresh-variable!))
  (define e* (add-lib e renaming ps fresh-label! fresh-variable!))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (set! next-loc nlabels)
  (set! contour-table (make-hash))
  (reset-globals! (make-vector (* 2 nlabels) ∅ #;nothing)) ;; ∅ → '()
  e*)

(define-syntax-rule (global-vector-getter σ* a)
  (vector-ref global-σ a))


(define-syntax-rule (get-contour-index!-0 ensure-σ-size c)
  (or (hash-ref contour-table c #f)
      (begin0 next-loc
              (ensure-σ-size)
              (hash-set! contour-table c next-loc)
              (inc-next-loc!))))

(define-syntax-rule (mk-ensure-σ-size name)
  (define (name)
    (when (= next-loc (vector-length global-σ))
      (set-global-σ! (grow-vector nothing global-σ next-loc)))))

(define-for-syntax ((make-var-contour-0-prealloc ensure) stx)
  (syntax-case stx ()
    [(_ x δ)
     (quasisyntax/loc stx
       (cond [(exact-nonnegative-integer? x) x]
             [else (get-contour-index!-0 #,ensure x)]))]))

(define-syntax-rule (with-0-ctx/prealloc body)
  (begin
    (mk-ensure-σ-size ensure-σ-size)
    (splicing-syntax-parameterize
        ([bind (make-rename-transformer #'bind-0)]
         [bind-rest (make-rename-transformer #'bind-rest-0)]
         [bind-rest-apply (make-rename-transformer #'bind-rest-apply-0)]
         [make-var-contour (make-var-contour-0-prealloc #'ensure-σ-size)])
      body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timestamp approximation
(define-syntax-rule (mk-join! a vs)
  (λ (as vs)
     (define prev (vector-ref global-σ a))
     (define upd (⊓ vs prev))
     (unless (≡ prev upd)
       (vector-set! global-σ a upd)
       (inc-unions!))))

(mk-mk-imperative/timestamp^-fixpoint
 mk-prealloc/timestamp^-fixpoint restrict-to-reachable/vector)

(define-syntax-rule (with-prealloc/timestamp-store body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join!)]
    [getter (make-rename-transformer #'global-vector-getter)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accumulated deltas
(define-syntax-rule (vector-ref-ignore-third v a ignore) (vector-ref v a))
#;
(mk-add-∆/s add-∆/acc/prealloc add-∆s/acc/prealloc bind-join/∆s/acc/prealloc
             vector-ref-ignore-third)

(define-syntax-rule (with-σ-∆s/acc/prealloc! (joiner) body)
  (with-σ-∆s/acc!
   (splicing-syntax-parameterize
    ([bind-join (make-rename-transformer #'joiner)]
     [getter (make-rename-transformer #'global-vector-getter)])
    body)))
(mk-mk-imperative/∆s/acc^-fixpoint
  mk-prealloc/∆s/acc^-fixpoint restrict-to-reachable/vector join! mk-join! vector-set! vector-ref-ignore-third)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Imperative deltas
#;
(mk-add-∆/s! add-∆/prealloc! add-∆s/prealloc! bind-join/∆s/prealloc
             vector-ref-ignore-third)

(define-syntax-rule (with-σ-∆s/prealloc! (joiner) body)
  (with-σ-∆s!
   (splicing-syntax-parameterize
    ([bind-join (bind-joiner #'joiner)]
     [getter (make-rename-transformer #'global-vector-getter)])
    body)))
(mk-mk-imperative/∆s^-fixpoint
  mk-prealloc/∆s^-fixpoint restrict-to-reachable/vector join! vector-set! vector-ref-ignore-third)
