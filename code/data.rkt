#lang racket
(require "ast.rkt" "notation.rkt" (for-syntax syntax/parse racket/syntax)
         racket/stxparam)
(provide define-nonce mk-touches mk-flatten-value cons-limit
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
         flatten-value
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
         atomic?
         nothing singleton
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
(define-simple-macro* (mk-flatten-value name clos rlos kont?)
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
           (rlos _ _ _ _ _)) 'function]
      [(? kont?) 'continuation]
      [else (error "Unknown base value" v)])))

;; Everything is all heterogeneous
(define nothing ∅)
(define singleton set)
(define ⊓ set-union)
(define ⊓1 set-add)

(define ⊑? subset?)
(define (≡ vs0 vs1) (= (set-count vs0) (set-count vs1)))

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

(define-simple-macro* (mk-touches touches:id clos:id rlos:id promise:id 0cfa?:boolean)
  (define (touches v)
    (match v
      [(clos xs e ρ fvs)
       #,(if (syntax-e #'0cfa?)
             #'fvs
             #'(for/hash ([x (in-set fvs)])
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [(rlos xs rest e ρ fvs)
       #,(if (syntax-e #'0cfa?)
             #'fvs
             #'(for/hash ([x (in-set fvs)])
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [(consv a d) (set a d)]
      [(or (vectorv _ l)
           (vectorv-immutable _ l)) (list->set l)]
      [(or (vectorv^ _ a)
           (vectorv-immutable^ _ a)) (set a)]
      [(? set? s) (for/union ([v (in-set s)]) (touches v))]
      [(promise e ρ)
       #,(if (syntax-e #'0cfa?)
             #'(free e)
             #'(for/hash ([x (in-set (free e))])
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [_ (set)])))

