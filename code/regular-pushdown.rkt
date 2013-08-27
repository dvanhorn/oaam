#lang racket
(require "do.rkt" "imperative.rkt" racket/stxparam racket/splicing
         "env.rkt" "notation.rkt" "data.rkt" (only-in "primitives.rkt" yield)
         "goedel-hash.rkt"
         (for-syntax racket/syntax syntax/parse))
(provide with-regular with-pushdown)

(define-syntax-rule (bind-push/regular (a* l δ k) body)
  (let ([a* (make-var-contour l δ)])
    (bind-join (a* (singleton k)) body)))

(define-syntax-rule (with-regular . body*)
  (splicing-syntax-parameterize
   ([bind-get-kont (syntax-rules () [(_ (k* comprehension k) . body)
                                     (let-syntax ([comprehension (make-rename-transformer #'in-set)])
                                       (bind-get (k* k) . body))])]
    [bind-push (make-rename-transformer #'bind-push/regular)]
    [bind-calling-context (syntax-rules () [(_ (k* ctx k) . body) (let ([k* k]) . body)])]
    [bind-get-ctx (λ (stx) #'#f)]
    [bind-memoize (λ (stx) #'#f)]
    [pushdown? #f])
   . body*))

(define ((bad-ctx ctx))
  (error 'in-context "Bad context ~a" ctx))


(define-simple-macro* (with-pushdown (~or (~once (~seq #:rtk rtk:id)) (~once (~seq #:kont kont:id)) (~once (~seq #:co co:id))) ... . body*)
  #,(with-syntax ([kont-cm (format-id #'kont "~a-cm" #'kont)])
      #`(splicing-syntax-parameterize
         ([bind-get-kont (syntax-rules () [(_ (k* comprehension a) . body)
                                           (let-syntax ([comprehension (make-rename-transformer #'in-value)])
                                             (let ([k* a]) . body))])]
          [bind-push (syntax-rules () [(_ (k* l δ k) . body) (let ([k* k]) . body)])]
          [bind-calling-context (syntax-rules () [(_ (k* ctx k) . body)
                                                  (let ([ctx-v ctx]
                                                        [kv k])
                                                    (push-Ξ! ctx-v kv)
                                                    (match (hash-ref global-M ctx-v #f)
                                                      [#f (define k* (rtk (kont-cm kv) ctx-v)) . body]
                                                      [vs (yield (co k vs))]))])]
          [bind-get-ctx (syntax-rules () [(_ (ks ctx) . body)
                                          (let ([ks (hash-ref global-Ξ ctx (bad-ctx ctx))])
                                            . body)])]
          [target-σ-token #,(let ([simple (cond
                                           [(syntax-parameter-value #'σ-∆s?)
                                            #'(λ (stx) #'(update target-σ top-σ))]
                                           [(syntax-parameter-value #'global-σ?)
                                            #'(λ (stx) #`(if saw-change? (add1 unions) unions))]
                                           [else #'(make-rename-transformer #'target-σ)])])
                              (if (syntax-parameter-value #'Gödel?)
                                  #`(λ (stx) 
                                       (define simple #,simple)
                                       (#,#'quasisyntax
                                        (GH-gh (#,#'unsyntax 
                                                (if (rename-transformer? simple)
                                                    (rename-transformer-target simple)
                                                    (simple stx))))))
                                  simple))]
          [bind-memoize (syntax-rules () [(_ (ctx vs) . body) (begin (memo! ctx vs) . body)])]
          [pushdown? #t])
         . body*)))