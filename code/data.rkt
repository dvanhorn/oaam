#lang racket
(require "ast.rkt" "notation.rkt" (for-syntax syntax/parse racket/syntax)
         "goedel-hash.rkt"
         racket/stxparam racket/splicing
         racket/trace)
(provide define-nonce mk-flatten-value cons-limit
         ;; abstract values
         number^;;integer^ rational^
         number^?
         string^ string^?
         symbol^ symbol^?
         char^ char^?
         cons^ cons^?
         vector^ vector^? vec0
         vector-immutable^ vector-immutable^?
         qdata^ qcons^ qvector^ qcons^? qvector^?
         ● ⊥
         open@ closed@
         fail ;; for continuation marks
         flatten-value Γτ?
         (struct-out vectorv^)
         (struct-out vectorv-immutable^)
         (struct-out input-port^)
         (struct-out output-port^)
         ;; concrete/abstract values
         (struct-out primop)
         (struct-out consv)
         (struct-out vectorv)
         (struct-out vectorv-immutable)
         (struct-out addr)
         ;; Constructed contracts
         (struct-out ccons)
         (struct-out cblarr)
         (struct-out cand)
         (struct-out cor)
         atomic?
         with-simple-data with-goedel-data
         nothing nothing? singleton value-set? in-value-set for/value-set for*/value-set
         hash-join1! hash-join! for/σ in-σ σ? σ-ref σ-set join join*
         ≡ ⊑? big⊓ ⊓ ⊓1)

(define-syntax (define-nonce stx)
  (syntax-case stx () [(_ name) (identifier? #'name)
                       (with-syntax ([-name (format-id #'name "-~a" #'name)])
                         #'(begin (struct -name ())
                                  (define name (-name))))]))

;; An AbstractVal is one of:
;; - number^
;; - string^
;; - symbol^
;; - cons^
;; - vector^
;; - ●
;; - (vectorv^ Number Addr) ;; collapsed into one addr
;; - (input-port^ Addr)
;; - (output-port^ Addr)
;; Some concrete values:
;; - Number
;; - String
;; - Symbol
;; - eof
;; - '()
;; - (void)
;; - (primop Sym)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (clos List[Var] Exp Env) ;; or without Env. Constructed by mk-analysis.
(define-nonce number^) (define (number^? v) (or (eq? v number^) (and (or (eq? v ●) (eq? v qdata^)) ●)))
(define-nonce string^) (define (string^? v) (or (eq? v string^) (and (or (eq? v ●) (eq? v qdata^)) ●)))
(define-nonce symbol^) (define (symbol^? v) (or (eq? v symbol^) (and (or (eq? v ●) (eq? v qdata^)) ●)))
(define-nonce char^) (define (char^? v) (or (eq? v char^) (and (or (eq? v ●) (eq? v qdata^)) ●)))
(define-nonce cons^) (define (cons^? v) (or (eq? v cons^) (and (eq? v ●) ●)))
(define-nonce vector^) (define (vector^? v) (or (eq? v vector^) (and (eq? v ●) ●)))
(define-nonce vector-immutable^) (define (vector-immutable^? v) (or (eq? v vector-immutable^) (and (eq? v ●) ●)))
(define-nonce qvector^) (define (qvector^? v) (or (eq? v qvector^) (and (eq? v qdata^) ●)))
(define-nonce qcons^) (define (qcons^? v) (or (eq? v qcons^) (and (eq? v qdata^) ●)))
(define-nonce vec0) ;; 0-length vector.
(struct input-port^ (status) #:prefab)
(struct output-port^ (status) #:prefab)
(define-nonce qdata^)
;; Status tokens for ports. Not values!
(define-nonce open@)
(define-nonce closed@)
;; Olin's black hole
(define-nonce ●)
(define-nonce ⊥)

;; Continutation marks fail token
(define-nonce fail)

(define-syntax-parameter flatten-value #f)
(define-syntax-parameter Γτ? #f)
(define-simple-macro* (mk-flatten-value name clos rlos blclos kont?)
  (define (name v)
    (match v
      [(? number?) number^]
      [(? string?) string^]
      [(? symbol?) symbol^]
      [(? char?) char^]
      [(or (? boolean?) '() (? void?) (? eof-object?)) v]
      [(or (? number^?) (== string^) (== symbol^) (== char^)
           (? vector^?) (== vector-immutable^)) v]
      [(? consv?) cons^]
      [(? vectorv?) vector^]
      [(or (? vectorv-immutable^?) (? vector?)) vector-immutable^]
      [(or (? input-port^?) (? input-port?)) 'input-port]
      [(or (? output-port^?) (? output-port?)) 'output-port]
      [(or (clos _ _ _ _)
           (rlos _ _ _ _ _)
           (blclos _ _ _ _ _ _)) 'function]
      [(? kont?) 'continuation]
      [else (error "Unknown base value" v)])))

;; Everything is all heterogeneous
(define-for-syntax (bad-data-parameterization stx)
  (raise-syntax-error #f "For use within the parameterization of a data representation" stx))
(define-syntax-parameter nothing bad-data-parameterization)
(define-syntax-parameter nothing? bad-data-parameterization)
(define-syntax-parameter singleton bad-data-parameterization)
(define-syntax-parameter value-set? bad-data-parameterization)
(define-syntax-parameter in-value-set bad-data-parameterization)
(define-syntax-parameter for/value-set bad-data-parameterization)
(define-syntax-parameter for*/value-set bad-data-parameterization)
(define-syntax-parameter for/σ bad-data-parameterization)
(define-syntax-parameter σ? bad-data-parameterization)
(define-syntax-parameter in-σ bad-data-parameterization)
(define-syntax-parameter σ-ref bad-data-parameterization)
(define-syntax-parameter σ-set bad-data-parameterization)
(define-syntax-parameter join bad-data-parameterization) ;; of hashes
(define-syntax-parameter join* bad-data-parameterization)
(define-syntax-parameter hash-join! bad-data-parameterization)
(define-syntax-parameter hash-join1! bad-data-parameterization)
(define-syntax-parameter ⊓ bad-data-parameterization) ;; of sets
(define-syntax-parameter ⊓1 bad-data-parameterization)
(define-syntax-parameter ⊑? bad-data-parameterization)
(define-syntax-parameter ≡ bad-data-parameterization)

(define-syntax-rule (with-common-between-simple-and-goedel . body)
  (begin
    (define (-join* eσ as ss)
      (for/fold ([eσ eσ]) ([a as] [s ss]) (join eσ a s)))
    (define (-hash-join1! h k v) (hash-set! h k (∪1 (hash-ref h k nothing) v)))
    (define (-hash-join! h k v) (hash-set! h k (∪ (hash-ref h k nothing) v)))
    (splicing-syntax-parameterize
     ([⊑? (make-rename-transformer #'subset?)]
      [in-value-set (make-rename-transformer #'in-set)]
      [⊓ (make-rename-transformer #'set-union)]
      [⊓1 (make-rename-transformer #'set-add)]
      [join* (make-rename-transformer #'-join*)]
      [hash-join1! (make-rename-transformer #'-hash-join1!)]
      [hash-join! (make-rename-transformer #'-hash-join!)])
     . body)))
(define-syntax-rule (with-goedel-data . body)
  (splicing-syntax-parameterize
   ([nothing (make-rename-transformer #'GH-set₀)]
    [nothing? (make-rename-transformer #'GH-set₀?)]
    [singleton (make-rename-transformer #'GH-singleton-set)]
    [value-set? (make-rename-transformer #'GH-set?)]
    [for/value-set (make-rename-transformer #'for/GH-set)]
    [for*/value-set (make-rename-transformer #'for*/GH-set)]
    [for/σ (make-rename-transformer #'for/GH-hash)]
    [σ? (make-rename-transformer #'GH-hash?)]
    [in-σ (make-rename-transformer #'in-dict)]
    [σ-ref (make-rename-transformer #'dict-ref)]
    [σ-set (make-rename-transformer #'dict-set)]
    [join (make-rename-transformer #'GH-hash-union)]
    [≡ (make-rename-transformer #'equal?)])
   (with-common-between-simple-and-goedel . body)))

(define-syntax-rule (with-simple-data . body)
  (splicing-syntax-parameterize
   ([nothing (make-rename-transformer #'∅)]
    [nothing? (make-rename-transformer #'∅?)]
    [singleton (make-rename-transformer #'set)]
    [value-set? (make-rename-transformer #'set?)]
    [for/value-set (make-rename-transformer #'for/set)]
    [for*/value-set (make-rename-transformer #'for*/set)]
    [for/σ (make-rename-transformer #'for/hash)]
    [σ? (make-rename-transformer #'hash?)]
    [in-σ (make-rename-transformer #'in-hash)]
    [σ-ref (make-rename-transformer #'hash-ref)]
    [σ-set (make-rename-transformer #'hash-set)]
    [join (make-rename-transformer #'hash-union)]
    [≡ (make-rename-transformer #'≡-set)])
   (with-common-between-simple-and-goedel . body)))

(define (≡-set vs0 vs1) (= (set-count vs0) (set-count vs1)))

(define-syntax-rule (big⊓ vs0 V)
  (let ()
    (unless (= (set-count vs0) 1)
      (error 'big⊓ "Expected singleton values for big⊓: ~a ~a" vs0 V))
    (define v0 (for/first ([v (in-set vs0)]) v))
    (cond [(eq? ⊥ V) v0]
          [else (if (equal? v0 V)
                    V
                    (let ([v0f (flatten-value v0)])
                      (if (equal? v0f V)
                          V
                          qdata^)))])))

(define cons-limit (make-parameter 8))

(struct vectorv^ (length addr) #:prefab)
(struct vectorv-immutable^ (length addr) #:prefab)

;; A Val is one of:
;; - Number
;; - Boolean
;; - (void)
;; - String
;; - Symbol
;; - '()
;; - eof
;; - Input-Port
;; - Output-Port
;; - (addr Addr)  ;; for delayed lookup.
;; - (primop Sym)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (immutable-vector Val ...)
;; - (clos List[Var] Exp Env) ;; or without Env. Constructed by mk-analysis.
(struct primop (which) #:prefab)
(struct consv (car cdr) #:prefab)
(struct vectorv (length addrs) #:prefab)
(struct vectorv-immutable (length addrs) #:prefab)
(struct addr (a) #:prefab)

;; Contract "values" though not 1st class
(struct ccons (ca cd) #:prefab)
(struct cblarr (ℓs ncs pc name η) #:prefab) ;; arrow contract for a given timeline, not get attached.
(struct cand (c₀ c₁) #:prefab)
(struct cor (c₀ c₁) #:prefab)
;; flat contracts are just the values themselves

;; For the lazy Krivine machine, a lazy cons (lazy in both arguments)
(struct lconsv (car cdr) #:prefab)

;; What are the supported primitives for a datum form?
;; REMARK: no list literals.
(define (atomic? x)
  (or (number? x)
      (boolean? x)
      (void? x)
      (char? x)
      (string? x)
      (symbol? x)
      (null? x)
      (eof-object? x)))