#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         (for-syntax syntax/parse) "data.rkt")
(provide bind-0 bind-1 bind-∞
         bind-rest-0 bind-rest-1 bind-rest-∞
         with-0-ctx with-1-ctx with-∞-ctx
         make-var-contour-0 make-var-contour-k)

(define-for-syntax ((mk-bind-rest K) stx)
  (syntax-parse stx
    [(_ (ρ* σ* δ*) (ρ iσ l δ xs r v-addrs) body)
     (define (bind-args wrap as r-meaning)
       (wrap
        (quasisyntax/loc stx
          (let-syntax ([add-r (syntax-rules ()
                                [(_ (νσ νρ sσ sρ sr sδ* vrest) body*)
                                 #,r-meaning])])
            (define-values (vfirst vrest)
              (let loop ([xs* xs] [axs '()] [vs v-addrs])
                (match* (xs* vs)
                  [('() vs) (values (reverse axs) vs)]
                  [((cons x xrest) (cons a arest))
                   (loop xrest (cons a axs) arest)])))
            (add-r (σ* ρ* iσ ρ r δ* vrest)
                   (bind-alias* (σ* σ* #,as vfirst) body))))))
     ;; Abstractly, rest-arg is an infinite list.
     (define abs-r
       #`(let* ([ra sr]
                [rA (make-var-contour `(A . ,sr) sδ*)]
                [rvs (if (null? vrest) snull (⊓1 snull (consv rA ra)))]
                #,@(if (zero? K) #'() #'([νρ (extend sρ r rA)])))
           (bind-join (νσ sσ ra rvs)
                      (bind-big-alias (νσ νσ rA vrest) body*))))
     ;; Concretely, rest-arg is a finite list.
     (define conc-r
       #'(let*-values ([(ra) (make-var-contour sr sδ*)]
                       [(νρ) (extend sρ r ra)])
           (do (sσ) loop ([as vrest] [last ra] [count 0])
               (match as
                 ['()
                  (do (sσ) ([νσ #:join sσ last snull])
                    body*)]
                 [(cons a as)
                  (define rnextA (make-var-contour `(,sr A . ,count) sδ*))
                  (define rnextD (make-var-contour `(,sr D . ,count) sδ*))
                  (do (sσ) ([νσ #:alias sσ rnextA a]
                            [νσ #:join νσ last (singleton (consv rnextA rnextD))])
                    (loop νσ as rnextD (add1 count)))]))))
     (cond [(zero? K)
            (bind-args values #'xs abs-r)]
           [(< K +inf.0)
            (bind-args (λ (body)
                          #`(let* ([δ* (truncate (cons l δ) #,K)]
                                   [as (map (λ (x) (make-var-contour x δ*)) xs)]
                                   [ρ* (extend* ρ xs as)])
                              #,body))
                       #'as abs-r)]
           [else
            (bind-args (λ (body) #`(let* ([δ* (cons l δ)]
                                          [as (map (λ (x) (make-var-contour x δ*)) xs)]
                                          [ρ* (extend* ρ xs as)])
                                     #,body))
                       #'as conc-r)])]))

(define-for-syntax ((mk-bind K) stx)
  (syntax-parse stx
    [(_ (ρ* σ* δ*) (ρ bσ l δ xs v-addrs) body)
     (define vs
       (λ (addrs)
          (quasisyntax/loc stx
            (bind-alias* (σ* bσ #,addrs v-addrs) body))))
     (if (zero? K)
         (vs #'xs)
         #`(let* ([δ* (truncate (cons l δ) #,K)]
                  [as (map (λ (x) (make-var-contour x δ*)) xs)]
                  [ρ* (extend* ρ xs as)])
             #,(vs #'as)))]))
(define-syntax-rule (make-var-contour-0 x δ) x)
(define-syntax-rule (make-var-contour-k x δ) (cons x δ))

(define-syntax bind-0 (mk-bind 0))
(define-syntax bind-1 (mk-bind 1))
(define-syntax bind-∞ (mk-bind +inf.0))
(define-syntax bind-rest-0 (mk-bind-rest 0))
(define-syntax bind-rest-1 (mk-bind-rest 1))
(define-syntax bind-rest-∞ (mk-bind-rest +inf.0))

(define ε '())
(define (truncate δ k)
  (cond [(zero? k) '()]
        [(empty? δ) '()]
        [else
         (cons (first δ) (truncate (rest δ) (sub1 k)))]))

(define-syntax-rule (with-0-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [bind-rest (make-rename-transformer #'bind-rest-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0)])
   body))

(define-syntax-rule (with-1-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-1)]
    [bind-rest (make-rename-transformer #'bind-rest-1)]
    [make-var-contour (make-rename-transformer #'make-var-contour-k)])
   body))

(define-syntax-rule (with-∞-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-∞)]
    [bind-rest (make-rename-transformer #'bind-rest-∞)]
    [make-var-contour (make-rename-transformer #'make-var-contour-k)])
   body))
