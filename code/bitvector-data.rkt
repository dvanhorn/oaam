#lang racket
(require "notation.rkt" "data.rkt" "do.rkt"
         racket/splicing
         racket/stxparam
         racket/unsafe/ops
         racket/trace
         (for-syntax syntax/parse))
(provide with-bitvector-data
         bv-first-bit
         exact-zero?
         value-register bit-register init-bit/value! grow-bit-register)

(define (exact-zero? x) (eq? 0 x))

(define value-register #f)
(define bit-register #f)
;; Build a mask for removing numbers (etc.) as we discover constant numbers.
(define kill-numbers #f)
(define kill-strings #f)
(define kill-symbols #f)
(define kill-chars #f)

(define number⊤ 1)
(define string⊤ 2)
(define symbol⊤ 4)
(define char⊤ 8)
(define bv-snull 2048)

(define initial-values
  (list number^ string^ symbol^ char^ ;; must be in this order
        qcons^ vector-immutable^ qvector^ qdata^ vector^
        open@ closed@ '() vec0))

(define (grow-bit-register)
  (set! bit-register
        (grow-vector ⊥ bit-register (vector-length bit-register))))

(define (init-bit/value! initial-values mk-single)
  (set! value-register (make-hash))
  (set! bit-register (make-vector 128))
  (for ([idx (in-naturals)]
        [v (in-list initial-values)])
    (hash-set! value-register v (mk-single idx))
    (vector-set! bit-register idx v)))

(define (mk-bare-single x) (arithmetic-shift 1 x))
(define (reset-registers!)
  (init-bit/value! initial-values mk-bare-single)
  (set! kill-numbers -1)
  (set! kill-strings -1)
  (set! kill-symbols -1)
  (set! kill-chars -1))
;; qcons doesn't clobber conses due to cons mutability.
(define top-mask (bitwise-ior number⊤ string⊤ symbol⊤ char⊤))

;; Set
(define (add-to-mask mask bit) (bitwise-and mask (bitwise-not bit)))
(define (bv-rem1 bv v) (add-to-mask bv (value->bv v)))
(define (value->bv v)
  (hash-ref! value-register v
             (λ ()
                (define num (hash-count value-register))
                (define new-bit (arithmetic-shift 1 num))
                (cond
                 [(number? v) (set! kill-numbers (add-to-mask kill-numbers new-bit))]
                 [(string? v) (set! kill-strings (add-to-mask kill-strings new-bit))]
                 [(symbol? v) (set! kill-symbols (add-to-mask kill-symbols new-bit))]
                 [(char? v) (set! kill-chars (add-to-mask kill-chars new-bit))]
                 [else (void)])
                (when (>= num (vector-length bit-register))
                  (grow-bit-register))
                (vector-set! bit-register num v)
                new-bit)))

;; Consider bv1 to be "new" and thus if it contains any tops,
;; we kill all values under them in the join.
(define (join bv0 bv1)
  (and bv0 bv1
       (let ([union (bitwise-ior bv0 bv1)])
         ;; The slow path is only hit if bv1 has top values.
         (if (exact-zero? (bitwise-and top-mask bv1))
             union
             (let* ([union
                     (if (bitwise-and number⊤ bv1)
                         (bitwise-and union kill-numbers)
                         union)]
                    [union
                     (if (bitwise-and string⊤ bv1)
                         (bitwise-and union kill-strings)
                         union)]
                    [union
                     (if (bitwise-and symbol⊤ bv1)
                         (bitwise-and union kill-symbols)
                         union)]
                    [union
                     (if (bitwise-and char⊤ bv1)
                         (bitwise-and union kill-chars)
                         union)])
               union)))))

;; Make top values clobber concrete values to decrease irrelevant flows.
(define (join1 bv val) (join bv (value->bv val)))

;; INVARIANT: expect top values to clobber all lesser values in compared sets
;; bv0 ⊑ bv1 iff empty?(bv0 - bv1) iff empty?(bv0 ∩ bv1^C)
(define (bv-⊑? bv0 bv1)
  (exact-zero? (bitwise-and bv0 (bitwise-not bv1))))

;; TODO: To have a faster next-bit check, we can subdivide
;; the bitvector into chunks of 62, 31, 16 and 8 bits given the
;; sparseness of the set, and use faster fixnum operations and
;; skip known useless iterations over several zeroes.
;; For now, do the naive thing.
;; lowest-bit-set: Exact-Positive-Integer -> Exact-Nonnegative-Integer
(define (lowest-bit-set bv)
  (let loop ([idx 0] [bv bv])
    (if (eq? 0 (bitwise-and bv 1))
        (loop (add1 idx) (arithmetic-shift bv -1))
        idx)))
(define (bv-first-bit idx bv)
  (cond [(exact-zero? bv) (values #f 0)]
        [else (define idx* (lowest-bit-set bv))
              (values (+ 1 idx idx*) (arithmetic-shift bv (sub1 (- idx*))))]))
(define (bv-next-bit-seq pos)
  (define idx (unsafe-struct-ref pos 0))
  (define bv (quotient (unsafe-struct-ref pos 1) 2))
  (cond [(exact-zero? bv) (bv-seq #f 0)]
        [else (define-values (idx bv) (bv-first-bit idx bv))
              (bv-seq idx bv)]))

(struct bv-seq (idx bv*) #:prefab)

(define (in-bv->values bv)
  (make-do-sequence
   (λ ()
      (values (λ (pos) (vector-ref bit-register (bv-seq-idx pos)))
              bv-next-bit-seq
              (let-values ([(idx bv*) (bv-first-bit -1 bv)])
                (bv-seq idx bv*))
              (λ (pos) (bv-seq-idx pos)) #f #f))))

(define-sequence-syntax *in-bv->values
  (λ () #'in-bv->values)
  (λ (stx)
     (syntax-parse stx #:literals (singleton value->bv)
       [[(id) (_ ((~or singleton value->bv) v))]
        #'[(id) (:do-in ([(id) v]) #t () #t () #t #f ())]]
       [[(id) (_ bv-expr)]
        #'[(id)
           (:do-in
            ([(idx bv) (bv-first-bit -1 bv-expr)])
            (void)
            ([bv bv]
             [idx idx])
            idx
            ([(idx* bv*) (bv-first-bit idx bv)]
             [(id) (vector-ref bit-register idx)])
            #t
            #t
            (bv* idx*))]]
       [_ #f])))

(module+ test
  (require rackunit)
  (test-check
   "in-abstract-values"
   equal?
   (begin (init-bit/value! '(a b c d e f g h i) mk-bare-single)
          (for/list ([x (*in-bv->values (bitwise-ior
                                         (arithmetic-shift 1 0)
                                         (arithmetic-shift 1 3)
                                         (arithmetic-shift 1 8)
                                         ))])
            x))
   '(a d i)))

(define-syntax-rule (with-bitvector-data . body)
  (splicing-syntax-parameterize
      ([nothing (λ _ #'0)]
       [is-nothing? (make-rename-transformer #'exact-zero?)]
       [singleton (make-rename-transformer #'value->bv)]
       [abstract-values? (make-rename-transformer #'exact-nonnegative-integer?)]
       [⊓ (make-rename-transformer #'join)]
       [⊓1 (make-rename-transformer #'join1)]
       [rem1 (make-rename-transformer #'bv-rem1)]
       [⊑? (make-rename-transformer #'bv-⊑?)]
       [≡ (make-rename-transformer #'=)]
       [in-abstract-values (make-rename-transformer #'*in-bv->values)]
       [snull (make-rename-transformer #'bv-snull)]
       [init-sequence (list*
                       #'(reset-registers!)
                       (syntax-parameter-value #'init-sequence))])
    . body))
