#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "parameters.rkt"
         (for-syntax syntax/parse) "data.rkt")
(provide bind-0 bind-1 bind-∞
         bind-rest-0 bind-rest-1 bind-rest-∞
         bind-rest-apply-0 bind-rest-apply-1 bind-rest-apply-∞
         with-0-ctx with-1-ctx with-∞-ctx
         make-var-contour-0 make-var-contour-k)

(define-for-syntax ((mk-bind-rest K apply?) stx)
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
                  [('() vs) (values (alt-reverse axs) vs)]
                  [((cons x xrest) (cons a arest))
                   (loop xrest (cons a axs) arest)])))
            (add-r (σ* ρ* iσ ρ r δ* vrest)
                   (bind-alias* (σ* σ* #,as vfirst) body))))))
     ;; Abstractly, rest-arg is an infinite list.
     (define abs-r
       (with-syntax ([(vrest-op ...) (if apply? #'(vrest) #'())])
         #`(let* ([ra sr]
                  [rA (make-rest^-contour ra sδ*)]
                  #,@(if (zero? K) #'() #'([νρ (extend sρ r rA)])))
             #,(if apply?
                   #'(do-comp #:bind/extra (#:σ outσ vrest* rvs)
                              (do (sσ) loop ([vrest vrest] [vrest* '()])
                                  (log-debug "Binding ~a ~a" vrest vrest*)
                                  (match vrest
                                    [(list tail)
                                     (bind-get (res sσ tail)
                                       (if (null? vrest*)
                                           (do-values vrest* res)
                                           (begin
                                             (printf "Getting all reses~%")
                                           (do (sσ) iloop ([vals (sequence->list (in-abstract-values res))]
                                                           [vrest* vrest*]
                                                           [rvs (singleton (consv rA ra))])
                                               (match vals
                                                 ['() (do-values vrest* rvs)]
                                                 [(cons '() rst)
                                                  (do-values vrest* (⊓1 rvs '()))]
                                                 [(cons (consv A D) rst)
                                                  (bind-get (rest sσ D)
                                                            (iloop sσ rst (cons A vrest*) (⊓ rest rvs)))]
                                                 [(cons _ rst)
                                                  (iloop sσ rst vrest* rvs)])))))]
                                    [(cons jA -vrest)
                                     (loop sσ -vrest (cons jA vrest*))]
                                    [_ (error 'bind-rest "Bad match ~a" vrest)]))
                              (bind-join (iσ outσ ra rvs)
                                         (bind-big-alias (νσ iσ rA vrest*) body*)))
                   #'(let ([rvs (if (null? vrest) snull (⊓1 snull (consv rA ra)))])
                       (bind-join (νσ sσ ra rvs)
                         (bind-big-alias (νσ νσ rA vrest) body*)))))))
     ;; Concretely, rest-arg is a finite list. FIXME: apply?
     (define conc-r
       #`(let*-values ([(ra) (make-rest-contour sr sδ*)]
                       [(νρ) (extend sρ r ra)])
           (do (sσ) loop ([as vrest] [last ra] [count 0])
               (match as
                 #,(if apply?
                       #'[(list last) (error 'TODO)]
                       #'['()
                          (do (sσ) ([νσ #:join sσ last snull])
                            body*)])
                 [(cons a as)
                  (define rnextA (make-rest-nA-contour sr count sδ*))
                  (define rnextD (make-rest-nD-contour sr count sδ*))
                  (do (sσ) ([νσ #:alias sσ rnextA a]
                            [νσ #:join νσ last (singleton (consv rnextA rnextD))])
                    (loop νσ as rnextD (add1 count)))]))))
     (cond [(zero? K)
            (bind-args values #'xs abs-r)]
           [(< K +inf.0)
            (bind-args (λ (body)
                          #`(let* ([δ* (truncate (cons l δ) #,K)]
                                   [as (map (λ (x) (make-var-contour l x δ*)) xs)]
                                   [ρ* (extend* ρ xs as)])
                              #,body))
                       #'as abs-r)]
           [else
            (bind-args (λ (body) #`(let* ([δ* (cons l δ)]
                                          [as (map (λ (x) (make-var-contour l x δ*)) xs)]
                                          [ρ* (extend* ρ xs as)])
                                     #,body))
                       #'as conc-r)])]))

(define-for-syntax ((mk-bind K) stx)
  (syntax-parse stx
    [(_ (ρ* σ* δ*) (ρ bσ l δ xs v-addrs) body)
     (define vs
       (λ (addrs)
          (quasisyntax/loc stx
            (bind-alias* (σ* bσ #,addrs v-addrs)
                         body
                         #;
                         (begin (printf "Alias ~a to ~a~%" #,addrs v-addrs) body)))))
     (if (zero? K)
         (vs #'xs)
         #`(let* ([δ* (truncate (cons l δ) #,K)]
                  [as (map (λ (x) (make-var-contour x δ*)) xs)]
                  [ρ* (extend* ρ xs as)])
             #,(vs #'as)))]))

(define-syntax-rule (make-var-contour-0 l x δ) x)
(define-syntax-rule (make-intermediate-contour-0 l x δ) (cons x 'temp))
(define-syntax-rule (make-vector^-contour-0 l δ) (cons 'V l))
(define-syntax-rule (make-vector-contour-0 l i δ) `(V ,i . ,l))
(define-syntax-rule (make-car-contour-0 l δ) `(A . ,l))
(define-syntax-rule (make-cdr-contour-0 l δ) `(D . ,l))
(define-syntax-rule (make-port-contour-0 l δ) `(Port . ,l))
(define-syntax-rule (make-apply-contour-0 l i δ) `(apply ,i . ,l))
(define-syntax-rule (make-kont-contour-0 l δ) l)
(define-syntax-rule (make-rest^-contour-0 l δ) `(A . ,l))

(define-syntax-rule (make-var-contour-k l x δ) (cons x δ))
(define-syntax-rule (make-rest-contour l δ) `((A . ,l) . ,δ))
(define-syntax-rule (make-rest-nA-contour l i δ) `((A ,i . ,l) . ,δ))
(define-syntax-rule (make-rest-nD-contour l i δ) `((D ,i . ,l) . ,δ))

(define-syntax bind-0 (mk-bind 0))
(define-syntax bind-1 (mk-bind 1))
(define-syntax bind-∞ (mk-bind +inf.0))
(define-syntax bind-rest-0 (mk-bind-rest 0 #f))
(define-syntax bind-rest-1 (mk-bind-rest 1 #f))
(define-syntax bind-rest-∞ (mk-bind-rest +inf.0 #f))
(define-syntax bind-rest-apply-0 (mk-bind-rest 0 #t))
(define-syntax bind-rest-apply-1 (mk-bind-rest 1 #t))
(define-syntax bind-rest-apply-∞ (mk-bind-rest +inf.0 #t))
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
    [bind-rest-apply (make-rename-transformer #'bind-rest-apply-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0)]
    [make-intermediate-contour (make-rename-transformer #'make-intermediate-contour-0)]
    [make-vector^-contour (make-rename-transformer #'make-vector^-contour-0)]
    [make-vector-contour (make-rename-transformer #'make-vector-contour-0)]
    [make-car-contour (make-rename-transformer #'make-car-contour-0)]
    [make-cdr-contour (make-rename-transformer #'make-cdr-contour-0)]
    [make-port-contour (make-rename-transformer #'make-port-contour-0)]
    [make-apply-contour (make-rename-transformer #'make-apply-contour-0)]
    [make-kont-contour (make-rename-transformer #'make-kont-contour-0)]
    [make-rest^-contour (make-rename-transformer #'make-rest^-contour-0)])
   body))

(define-syntax-rule (with-1-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-1)]
    [bind-rest (make-rename-transformer #'bind-rest-1)]
    [bind-rest-apply (make-rename-transformer #'bind-rest-apply-1)]
    [make-var-contour (make-rename-transformer #'make-var-contour-k)])
   body))

(define-syntax-rule (with-∞-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-∞)]
    [bind-rest (make-rename-transformer #'bind-rest-∞)]
    [bind-rest-apply (make-rename-transformer #'bind-rest-apply-∞)]
    [make-var-contour (make-rename-transformer #'make-var-contour-k)])
   body))
