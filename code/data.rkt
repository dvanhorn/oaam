#lang racket
(require "ast.rkt" "notation.rkt" (for-syntax syntax/parse racket/syntax))
(provide define-nonce mk-touches cons-limit
         ;; abstract values
         number^;;integer^ rational^
         number^?
         string^ symbol^ char^ cons^ vector^ vector-immutable^ ●
         (struct-out vectorv^)
         (struct-out vectorv-immutable^)
         (struct-out input-port^)
         (struct-out output-port^)
         ;; concrete/abstract values
         (struct-out primop)
         (struct-out consv)
         (struct-out vectorv)
         (struct-out vectorv-immutable)
         (struct-out hashv)
         (struct-out hash-with)
         (struct-out hash-without)
         (struct-out mthash)
         (struct-out addr)
         atomic?
         ⊑? ⊓)

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
;; - '()
;; - (void)
;; - (primop Sym)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (clos List[Var] Exp Env) ;; or without Env. Constructed by mk-analysis.
;; - (mthash Sym)
;; - (hash-with Sym Addr Addr Addr)
;; - (hash-without Sym Addr Addr)
(define-nonce number^) (define (number^? v) (eq? v number^))
#|
(define-nonce integer^) (define (number^? v) (or (eq? v integer^) (eq? v rational^) (eq? v number^)))
(define-nonce rational^)|#
(define-nonce string^)
(define-nonce symbol^)
(define-nonce char^)
(define-nonce cons^)
(define-nonce vector^)
(define-nonce vector-immutable^)
(struct input-port^ (status) #:prefab)
(struct output-port^ (status) #:prefab)
;; Olin's black hole
(define-nonce ●)

(define (⊑? v0 v1)
  (cond [(equal? v0 v1) #t]
        [(set? v0)
         (for/and ([v (in-set v0)]) (⊑? v v1))]
        [(set? v1)
         (for/or ([v (in-set v1)]) (⊑? v0 v))]
        [else
         (match* (v0 v1)
#|
           [((== integer^) (or (== rational^) (== number^))) #t]
           [((== rational^) (== number^)) #t]
           [((? integer?) (? number^?)) #t]
           [((? rational?) (or (== rational^) (== number^))) #t]
|#
           [((? number?) (== number^)) #t]
           [((? consv?) (== cons^)) #t]
           [((or (? vectorv?) (? vectorv^?)) (== vector^)) #t]
           [((or (? vectorv-immutable?) (? vectorv-immutable^?))
             (== vector-immutable^)) #t]
           [((? char?) (== char^)) #t]
           [((? symbol?) (== symbol^)) #t]
           [((? string?) (== string^)) #t]
           [(_ (== ●)) #t]
           [(_ _) #f])]))
(define (⊓ v0 v1)
  (for/fold ([vs v0]) ([v (in-set v1)]
                       #:unless (⊑? v vs))
    (∪1 vs v)))

;; No support for inspectors, guards, auto fields, struct properties,
;; or make-struct-type.
;; REMARK: It's unclear how to effectively model arbitrary struct types since
;; the lists of immutable/mutable fields could be "infinite length."
;; We would have to determine at every make point whether these lists
;; have cycles, and then choose to use an unbounded representation as
;; we do for vectors. This seems like a lot of trouble, and could be
;; detrimental to the performance of analyzing common Racket programs,
;; as they tend to only have top level struct definitions that are far
;; better behaved.
(struct struct-typev (nonce name-Addr parent-addr fields) #:prefab)
;; A Compound-Datatype-Descriptor is one of:
;; - cons^
;; - vector^
;; - immutable-vector^
;; - Addr (to a struct type)
;; A Compound is a
;; - (compoundv Compound-Datatype-Descriptor IVector[Addr])
;; An Unbounded-Compound is a
;; - (unbounded-compoundv Compound-Datatype-Descriptor Addr Addr)

(define cons-limit (make-parameter 8))

(struct vectorv^ (length addr) #:prefab)
(struct vectorv-immutable^ (length addr) #:prefab)

(struct compoundv (kind fields) #:prefab)
(struct unbounded-compoundv (kind length^ data) #:prefab)
(struct compoundv-predicate (descriptor) #:prefab)
(struct compoundv-selector (descriptor) #:prefab)
(struct compoundv-mutator (descriptor) #:prefab)
;; REMARK: In Racket there is only one selector/mutator per struct
;; type, but the field indices would be merged, causing terrible
;; precision.  We currently model structs with our own form and do not
;; allow make-struct-type. Stack allocation and PDA-based analysis
;; would alleviate this problem for Racket.
(struct compoundv-selector-i (descriptor field) #:prefab)
(struct compoundv-mutator-i (descriptor field) #:prefab)
;; We need anonymous compound data for modeling read and other
;; "outside world" sources of data.

;; A Val is one of:
;; - Number
;; - Boolean
;; - (void)
;; - String
;; - Symbol
;; - '()
;; - Input-Port
;; - Output-Port
;; - (addr Addr)  ;; for delayed lookup.
;; - (primop Sym)
;; - (consv Addr Addr)
;; - (vectorv Number (listof Addr))
;; - (immutable-vector Val ...)
;; - (clos List[Var] Exp Env) ;; or without Env. Constructed by mk-analysis.
;; - (mthash Sym)
;; - (hash-with Sym Addr Addr Addr)
;; - (hash-without Sym Addr Addr)
(struct primop (which) #:prefab)
(struct consv (car cdr) #:prefab)
(struct vectorv (length addrs) #:prefab)
(struct vectorv-immutable (length addrs) #:prefab)
(struct addr (a) #:prefab)
;; immutable vectors and immutable hashes are themselves if given as literals.
;; Otherwise they are not yet supported.
;; Idea:
;; Hashes represented as sorta-alists (have a history)
(struct hashv (kind) #:prefab)
(struct hash-with hashv (parent key value) #:prefab)
(struct hash-without hashv (former key) #:prefab)
(struct mthash hashv () #:prefab)

;; What are the supported primitives for a datum form?
;; REMARK: no list literals.
(define (atomic? x)
  (or (number? x)
      (boolean? x)
      (void? x)
      (string? x)
      (symbol? x)
      (null? x)
      (eof-object? x)))

(define-simple-macro* (mk-touches touches:id clos:id rlos:id 0cfa?:boolean)
  (define (touches v)
    (match v
      [(clos xs e ρ fvs)
       #,(if (syntax-e #'0cfa?)
             #'fvs
             #'(for/hash ([x (in-set fvs)]
                          #:unless (memv x xs))
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [(rlos xs rest e ρ fvs)
       #,(if (syntax-e #'0cfa?)
             #'fvs
             #'(for/hash ([x (in-set fvs)]
                          #:unless (or (eq? x rest)
                                       (memv x xs)))
                 (hash-ref ρ x
                           (λ () (error 'touches "Free identifier (~a) not in env ~a" x ρ)))))]
      [(consv a d) (set a d)]
      [(hash-with _ parent key value) (set parent key value)]
      [(hash-without _ former key) (set former key)]
      [(vectorv _ l) (list->set l)]
      [(vectorv^ _ a) (set a)]
      [(? set? s) (for/union ([v (in-set s)]) (touches v))]
      [_ (set)])))

