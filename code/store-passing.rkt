#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam)
(provide bind-join-whole bind-join*-whole
         (for-syntax bind-rest) ;; common helper
         wide-step hash-getter
         mk-set-fixpoint^
         with-narrow-set-monad
         with-σ-passing-set-monad
         with-whole-σ)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widen set-monad fixpoint
(define-syntax-rule (wide-step step)
  (λ (state)
     (match state
       [(cons wsσ cs)
        (define-values (σ* cs*)
          (for/fold ([σ* wsσ] [cs ∅]) ([c (in-set cs)])
            (define-values (σ** cs*) (step (cons wsσ c)))
            (values (join-store σ* σ**) (∪ cs* cs))))
        (set (cons σ* cs*))]
       [_ (error 'wide-step "bad output ~a~%" state)])))

(define-syntax-rule (mk-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let ()
     (define-values (f^σ cs) fst)
     (define s (fix (wide-step step) (set (cons f^σ cs))))
     (for/fold ([last-σ (hash)] [final-cs ∅]) ([s s])
       (match s
         [(cons fsσ cs)
          (define-values (σ* cs*)
            (values (join-store last-σ fsσ)
                    (for/set #:initial final-cs ([c (in-set cs)]
                                                 #:when (ans^? c))
                             c)))
          (values σ* cs*)]
         [_ (error 'name "bad output ~a~%" s)])))))

(define-for-syntax do-body-transform-σ/cs
  (syntax-rules () [(_ e) (let-values ([(σ* cs) e])
                            #;
                            (log-debug "Transformed ~a ~a" cs target-cs)
                            (values σ* (∪ target-cs cs)))]))
(define-for-syntax do-body-transform-cs
  (syntax-rules () [(_ e) (let ([cs e]) (∪ target-cs cs))]))

(define-for-syntax (bind-rest inner-σ body)
  #`(syntax-parameterize ([target-σ (make-rename-transformer #'#,inner-σ)])
      #,body))
(define-simple-macro* (bind-join-whole (σjoin sσ a vs) body)
  (let ([σjoin (join sσ a vs)]) #,(bind-rest #'σjoin #'body)))
(define-simple-macro* (bind-join*-whole (σjoin* sσ as vss) body)
  (let ([σjoin* (join* sσ as vss)]) #,(bind-rest #'σjoin* #'body)))

(define (hash-getter hgσ a)
  (hash-ref hgσ a (λ () (error 'getter "Unbound address ~a in store ~a" a hgσ))))

(define-syntax-rule (with-σ-passing-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (values target-σ (∪1 target-cs e))])]
    [do-body-transformer do-body-transform-σ/cs])
   body))

(define-syntax-rule (with-narrow-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (∪1 target-cs e)])]
    [do-body-transformer do-body-transform-cs])
   body))

(define-syntax-rule (with-whole-σ body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-whole)]
    [bind-join* (make-rename-transformer #'bind-join*-whole)]
    [getter (make-rename-transformer #'hash-getter)])
   body))