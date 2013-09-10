#lang racket
(provide extend extend* set-join restrict-hasheq-to-set restrict-hash-to-set
         with-env-defs
         join-store update join/change no-change? join-store/change update/change would-update?
         restrict-σ-to-set reach reach/vec restrict-to-reachable restrict-to-reachable/vector)
(require "data.rkt" "ast.rkt" "notation.rkt" "goedel-hash.rkt"
         racket/stxparam racket/splicing
         (for-syntax syntax/parse racket/syntax))

(define (extend ρ x v)
  (hash-set ρ x v))
(define (extend* ρ xs vs)
  (for/fold ([ρ ρ]) ([x (in-list xs)] [v (in-list vs)])
    (hash-set ρ x v)))
(define (set-join eσ a s)
  (hash-set eσ a (∪ s (hash-ref eσ a ∅))))

(define (restrict-hasheq-to-set ρ S)
  (for/hasheq ([(x a) (in-hash ρ)]
               #:when (x . ∈ . S))
    (values x a)))
(define (restrict-hash-to-set ρ S)
  (for/hash ([(x a) (in-hash ρ)]
             #:when (x . ∈ . S))
    (values x a)))

(define-for-syntax (bad-env-use stx)
  (raise-syntax-error #f "For use in the context of with-env-defs" stx))
(define-syntax-parameter join-store bad-env-use)
(define-syntax-parameter update bad-env-use)
(define-syntax-parameter join/change bad-env-use)
(define-syntax-parameter no-change? bad-env-use)
(define-syntax-parameter join-store/change bad-env-use)
(define-syntax-parameter update/change bad-env-use)
(define-syntax-parameter would-update? bad-env-use)
(define-syntax-parameter restrict-σ-to-set bad-env-use)
(define-syntax-parameter reach bad-env-use)
(define-syntax-parameter reach/vec bad-env-use)
(define-syntax-parameter restrict-to-reachable bad-env-use)
(define-syntax-parameter restrict-to-reachable/vector bad-env-use)
(define-syntax (define-and-parameterize stx)
  (syntax-parse stx #:literals (define)
    [(_ ([param:id e:expr] ...) . body)
     (define/with-syntax (names ...) (generate-temporaries #'(param ...)))
     (syntax/loc stx
       (begin
         (define names e) ...
         (splicing-syntax-parameterize ([param (make-rename-transformer #'names)] ...) . body)))]))

(define-syntax-rule (with-env-defs . body)
  (begin
    (define (((mk-reach ref) touches) eσ root)
      (define seen (make-hasheq))
      (let loop ([as root])
        (for/union #:res acc ([a (in-set as)]
                              #:unless (hash-has-key? seen a))
                   (hash-set! seen a #t)
                   (for/union #:initial (∪1 acc a)
                              ([v (in-set (ref eσ a nothing))])
                              (loop (touches v))))))
    
    (define ((mk-restrict-to-reachable ref) touches)
      (define reach ((mk-reach ref) touches))
      (λ (eσ v)
         (for/hash ([a (in-set (reach eσ (touches v)))])
           (values a (ref eσ a)))))
    (define-and-parameterize
      ([join-store ;; Perform join and return if the join was idempotent
        ;; Store Store -> Store
        (λ (eσ1 eσ2)
          (for/fold ([eσ eσ1])
              ([(k v) (in-hash eσ2)])
            (join eσ k v)))]

       [update
        (λ (∆s eσ)
          (for/fold ([eσ eσ]) ([a×vs (in-list ∆s)])
            (join eσ (car a×vs) (cdr a×vs))))]

       [join/change
        (λ (eσ a s)
          (define prev (hash-ref eσ a nothing))
          (define s* (⊓ s prev))
          (values (hash-set eσ a s*) (≡ prev s*)))]

       [no-change?
        (λ (eσ a s)
          (⊑? s (hash-ref eσ a nothing)))]

       [restrict-σ-to-set
        (λ (ρ S)
          (for/σ ([(x a) (in-σ ρ)]
                  #:when (x . ∈ . S))
                 (values x a)))]

       [reach (mk-reach dict-ref)]

       [reach/vec (mk-reach vector-ref)]
    
       [restrict-to-reachable (mk-restrict-to-reachable hash-ref)]

       [restrict-to-reachable/vector (mk-restrict-to-reachable vector-ref)])
      (define -join-store/change
        (λ (eσ1 eσ2)
           (for/fold ([eσ eσ1] [same? #t])
               ([(k v) (in-hash eσ2)])
             (define-values (eσ* same?*) (join/change eσ k v))
             (values eσ* (and same? same?*)))))
      (define -update/change
        (λ (∆s eσ)
           (for/fold ([eσ eσ] [same? #t]) ([a×vs (in-list ∆s)])
             (define-values (σ* a-same?) (join/change eσ (car a×vs) (cdr a×vs)))
             (values σ* (and same? a-same?)))))
      (define -would-update
        (λ (∆s eσ)
          (not (for/and ([a×vs (in-list ∆s)]) (no-change? eσ (car a×vs) (cdr a×vs))))))
      (splicing-syntax-parameterize
       ([join-store/change (make-rename-transformer #'-join-store/change)]
        [update/change (make-rename-transformer #'-update/change)]
        [would-update? (make-rename-transformer #'-would-update)])
       . body))))
