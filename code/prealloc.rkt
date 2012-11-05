#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "data.rkt" "imperative.rkt" "context.rkt" "add-lib.rkt")
(provide prepare-prealloc mk-prealloc^-fixpoint with-0-ctx/prealloc
         grow-vector ;; helper
         with-prealloc-store)

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
 
(define (join! a vs)
  (define prev (vector-ref global-σ a))
  (define upd (⊓ vs prev))
  (define same? (= (set-count prev) (set-count upd)))
  (unless same?
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

(define-syntax-rule (global-vector-getter σ* a)
  (vector-ref global-σ a))

(define-syntax-rule (mk-prealloc^-fixpoint name ans^? ans^-v touches)
  (define (name step fst)
    (define clean-σ (restrict-to-reachable/vector touches))
    (let loop ()
      (cond [(∅? todo) ;; → null?
             (define vs
               (for*/set ([(c at-unions) (in-hash seen)]
                          #:when (ans^? c))
                 (ans^-v c)))
             (cons (clean-σ global-σ vs)
                   vs)]
            [else
             (define todo-old todo)
             (reset-todo!)                        ;; → '()
             (for ([c (in-set todo-old)]) (step c)) ;; → in-list
             (loop)]))))

(define-syntax-rule (with-0-ctx/prealloc body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [bind-rest (make-rename-transformer #'bind-rest-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0-prealloc)])
   body))

(define-syntax-rule (with-prealloc-store body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join!)]
    [bind-join* (make-rename-transformer #'bind-join*!)]
    [getter (make-rename-transformer #'global-vector-getter)])
   body))