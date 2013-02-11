#lang racket
(require "ast.rkt" "notation.rkt" (for-syntax syntax/parse racket/syntax)
         racket/stxparam)
(provide define-nonce touches mk-touches cons-limit mk-flatten-value
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
         (struct-out value-set)
         atomic?
         grow-vector
         ;; Parameters
         nothing is-nothing? singleton mk-flatten-value
         for/join for/join1 in-abstract-values abstract-values->list
         abstract-values? interval-abstraction
         ≡ ⊑? big⊓ ⊓ ⊓1 rem1 snull flatten-value)
(define-syntax-parameter touches #f)
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
;; - (primop Sym Val procedure-arity?)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (clos List[Var] Exp Env) ;; or without Env. Constructed by mk-analysis.
(define-nonce number^) (define (number^? v) (or (eq? v number^) (and (or (eq? v ●) (eq? v qdata^)) v)))
(define-nonce string^) (define (string^? v) (or (eq? v string^) (and (or (eq? v ●) (eq? v qdata^)) v)))
(define-nonce symbol^) (define (symbol^? v) (or (eq? v symbol^) (and (or (eq? v ●) (eq? v qdata^)) v)))
(define-nonce char^) (define (char^? v) (or (eq? v char^) (and (or (eq? v ●) (eq? v qdata^)) v)))
(define-nonce cons^) (define (cons^? v) (or (eq? v cons^) (and (eq? v ●) ●)))
(define-nonce vector^) (define (vector^? v) (or (eq? v vector^) (and (eq? v ●) ●)))
(define-nonce vector-immutable^) (define (vector-immutable^? v) (or (eq? v vector-immutable^) (and (eq? v ●) ●)))
(define-nonce qvector^) (define (qvector^? v) (or (eq? v qvector^) (and (eq? v qdata^) v)))
(define-nonce qcons^) (define (qcons^? v) (or (eq? v qcons^) (and (eq? v qdata^) v)))
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

(define cons-limit (make-parameter 1))

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
;; - (primop Sym Val procedure-arity?)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (immutable-vector Val ...)
;; - (clos List[Var] Exp Env) ;; or without Env. Constructed by mk-analysis.
(struct primop (which apply-fallback arity) #:prefab)
(struct consv (car cdr) #:prefab)
(struct vectorv (length addrs) #:prefab)
(struct vectorv-immutable (length addrs) #:prefab)
(struct addr (a) #:prefab)
(struct value-set (a) #:prefab)

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
      (eof-object? x)
      (and (vector? x) (immutable? x))
      #;(and (hash? x) (immutable? x))
      ))

;; Tweakable lattice.
(define-syntax-parameter ⊓ #f)
(define-syntax-parameter ⊓1 #f)
(define-syntax-parameter rem1 #f)
(define-syntax-parameter in-abstract-values #f)
(define-syntax-parameter abstract-values? #f)
(define-syntax-parameter nothing #f)
(define-syntax-parameter is-nothing? #f)
(define-syntax-parameter singleton #f)
(define-syntax-parameter ⊑? #f)
(define-syntax-parameter ≡ #f)
(define-syntax-parameter snull #f) ;; common but derived
(define-syntax-parameter flatten-value #f) ;; populated by mk-flatten-value
(define-syntax-parameter interval-abstraction
  (λ (stx)
     (syntax-case stx ()
       [(_ e) #'(error 'interval-abstraction "Current data abstraction incompatible with R-trees")])))

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
      [(or (clos _ _ _)
           (rlos _ _ _ _)) 'function]
      [(? kont?) 'continuation]
      [else (error "Unknown base value" v)])))

(define-syntax-rule (big⊓ vs0 V)
  (let ()
    (define v0 (for/first ([v (in-abstract-values vs0)]) v))
    (cond [(eq? ⊥ V) v0]
          [else (if (equal? v0 V)
                    V
                    (let ([v0f (flatten-value v0)])
                      (if (equal? v0f V)
                          V
                          qdata^)))])))

(define (grow-vector fill σ old-size)
  (for/vector #:length (* 2 old-size) #:fill fill
                 ([v (in-vector σ)]
                  [i (in-naturals)]
                  #:when (< i old-size))
    v))

(define-simple-macro* (for/join (~var o (ops #'nothing)) guards body ...+)
  (for/fold ([o.res o.init]) guards (⊓ o.res (let () body ...))))
(define-simple-macro* (for/join1 (~var o (ops #'nothing)) guards body ...+)
  (for/fold ([o.res o.init]) guards (⊓1 o.res (let () body ...))))
(define-syntax-rule (abstract-values->list expr)
  (for/list ([v (in-abstract-values expr)]) v))

(define-simple-macro* (mk-touches touches:id clos:id rlos:id
                                  ls:id lrk:id ltk:id ifk:id sk!:id pfk:id
                                  ast-fv:id promise:id
                                  0cfa?:boolean
                                  pushdown?:boolean)
  (define (touches v)
    (match v
      [(clos xs e ρ)
       #,(if (syntax-e #'0cfa?)
             #'(ast-fv e)
             #'(for/hash ([x (in-set (ast-fv e))])
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [(rlos xs rest e ρ)
       #,(if (syntax-e #'0cfa?)
             #'(ast-fv e)
             #'(for/hash ([x (in-set (ast-fv e))])
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [(consv a d) (set a d)]
      [(or (vectorv _ l)
           (vectorv-immutable _ l)) (list->set l)]
      [(or (vectorv^ _ a)
           (vectorv-immutable^ _ a)) (set a)]
      [(? abstract-values? s) (for/union ([v (in-abstract-values s)]) (touches v))]
      [(promise e ρ)
       #,(if (syntax-e #'0cfa?)
             #'(ast-fv e)
             #'(for/hash ([x (in-set (ast-fv e))])
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      ;; Continuation frames
      #,@(let ([kont-rest
                (if (syntax-e #'pushdown?)
                    (λ (stx) #`(∪ #,stx (touches a)))
                    (λ (stx) #`(∪1 #,stx a)))])
           #`([(ls _ l n es v-addrs ρ a δ)
               #,(kont-rest
                  (if (syntax-e #'0cfa?)
                      #'(for/set #:initial (for/union ([e (in-list es)]) (ast-fv e))
                                 ([a (in-list v-addrs)])
                                 a)
                      #'(for/set #:initial (for/set ([(_ a) (in-hash ρ)]) a)
                                 ([a (in-list v-addrs)])
                                 a)))]
              [(lrk _ x xs es body ρ a δ)
               #,(kont-rest
                  (if (syntax-e #'0cfa?)
                     #'(for/union #:initial (ast-fv body) ([e (in-list es)]) (ast-fv e))
                     #'(for/set ([(_ a) (in-hash ρ)]) a)))]
              [(ltk _ _ x xs es x-done v-addrs body ρ a δ)
               #,(kont-rest
                  (if (syntax-e #'0cfa?)
                      #'(∪/l (for/union #:initial (ast-fv body)
                                        ([e (in-list es)])
                                        (ast-fv e))
                             v-addrs)
                      #'(for/set #:initial (list->set v-addrs)
                                 ([(_ a) (in-hash ρ)]) a)))]
              [(ifk _ t e ρ a δ)
               #,(kont-rest
                  (if (syntax-e #'0cfa?)
                      #'(∪ (ast-fv t) (ast-fv e))
                      #'(for/set ([(_ a) (in-hash ρ)]) a)))]
              [(sk! _ l a) #,(kont-rest #'(set l))]
              [(pfk _ _ a) #,(kont-rest #'∅)]))
      [_ (set)])))

