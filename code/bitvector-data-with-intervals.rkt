#lang racket
(require "notation.rkt" "data.rkt" "do.rkt" "../../r-tree/sparse-hrect.rkt"
         (only-in "parse.rkt" register-datum)
         racket/splicing
         racket/stxparam
         racket/unsafe/ops
         racket/trace
         (for-syntax syntax/parse)
         (rename-in (only-in "bitvector-data.rkt"
                             bv-first-bit exact-zero?
                             bit-register value-register
                             init-bit/value! grow-bit-register)
                    [bv-first-bit orig-bv-first-bit]))
(provide with-bitvector-data/intervals)

(struct αbv (start extent bv) #:prefab)
(define (αbv-is-nothing? αbv) (or (not αbv) (exact-zero? (αbv-bv αbv))))
(define/match (αbv-≡ αbv0 αbv1)
  [((αbv _ _ bv0) (αbv _ _ bv1)) (= bv0 bv1)]
  [(#f #f) #t]
  [(_ _) #f])
(define/match (αbv-interval abv)
  [((αbv start extent _)) (cons start extent)]
  [(#f) #f])

;; Literals accumulated during parsing.
(define number-literals ∅)
(define string-literals ∅)
(define symbol-literals ∅)
(define char-literals ∅)
(define qvector-literals (set vec0))

(define top-mask #f)
(define number⊤ #f) (define conditionally-number⊤ize #f)
(define string⊤ #f) (define conditionally-string⊤ize #f)
(define symbol⊤ #f) (define conditionally-symbol⊤ize #f)
(define char⊤ #f) (define conditionally-char⊤ize #f)
(define qvector⊤ #f) (define conditionally-qvector⊤ize #f)
(define qdata⊤ #f) (define conditionally-qdata⊤ize #f)

(define starting-values
  (list (void) eof open@ closed@ qdata^ #t #f '() qcons^))
(define qdata-start 4)
(define null-pos 7)
(define qcons-pos 8)
(define bv-snull (αbv null-pos 1 (arithmetic-shift 1 null-pos)))
(define bv-nothing #f)

;; Accumulated during runtime.
(define kill-ivectors -1) (define conditionally-ivector⊤ize #f)
(define kill-vectors -1) (define conditionally-vector⊤ize #f)
(define kill-conses -1) (define conditionally-cons⊤ize #f)
;; Set in reset-registers!
(define ivector⊤-bv #f)
(define vector⊤-bv #f)
(define cons⊤-bv #f)

(define (bv-register-datum! d)
  (define-syntax-rule (inc-lit id) (set! id (∪1 id d)))
  (cond
   [(number? d) (inc-lit number-literals)]
   [(string? d) (inc-lit string-literals)]
   [(symbol? d) (inc-lit symbol-literals)]
   [(char? d) (inc-lit char-literals)]
   [(and (vector? d) (immutable? d)) (inc-lit qvector-literals)]
   ;; Finite types are preallocated.
   [(or (boolean? d) (null? d) (void? d) (eof-object? d)) (void)]
   [else (error 'bv-register-datum! "Unsupported atomic data type ~a" d)]))

;; The top element of a type is reserved for the start of the
;; range of bits for that type. If the top element is present,
;; kill all the concrete elements.
(define (normalizeq⊤ start extent)
  (define kill-mask
    (bitwise-not (arithmetic-shift (sub1 (arithmetic-shift 1 (sub1 extent)))
                                   (add1 start))))
  (define top-mask (arithmetic-shift 1 start))
  (λ (bv) (if (exact-zero? (bitwise-and bv top-mask))
              bv
              (bitwise-and bv kill-mask))))

(define-syntax-rule (define-dynamic-top name mask top-bv)
  (define (name bv) (bitwise-ior (bitwise-and bv mask) top-bv)))
(define-dynamic-top ivector⊤ kill-ivectors ivector⊤-bv)
(define-dynamic-top vector⊤ kill-vectors vector⊤-bv)
(define-dynamic-top cons⊤ kill-conses cons⊤-bv)

(define-syntax-rule (fset! id) (λ (x) (set! id x)))
(define (mk-conditionally-⊤ize start ⊤ize)
  (λ (bv-dst bv-tst)
     (if (bitwise-bit-set? bv-tst start)
         (⊤ize bv-dst)
         bv-dst)))

(define (range/count top lits start set⊤! set-cond⊤!)
  (define extent (add1 (set-count lits)))
  (define ⊤ize (normalizeq⊤ start extent))
  (set⊤! ⊤ize)
  (set-cond⊤! (mk-conditionally-⊤ize start ⊤ize))
  (values (cons top (set->list lits))
          extent
          (+ start extent)))

(define (reset-registers!)
  (define number-start (length starting-values))
  (define-values (number-range num-number string-start)
    (range/count number^ number-literals number-start
                 (fset! number⊤) (fset! conditionally-number⊤ize)))
  (define-values (string-range num-string symbol-start)
    (range/count string^ string-literals string-start
                 (fset! string⊤) (fset! conditionally-string⊤ize)))
  (define-values (symbol-range num-symbol char-start)
    (range/count symbol^ symbol-literals symbol-start
                 (fset! symbol⊤) (fset! conditionally-symbol⊤ize)))
  (define-values (char-range num-char qvector-start)
    (range/count char^ char-literals char-start
                 (fset! char⊤) (fset! conditionally-char⊤ize)))
  (define-values (qvector-range num-qvector ivector⊤-pos)
    (range/count qvector^ qvector-literals qvector-start
                 (fset! qvector⊤) (fset! conditionally-qvector⊤ize)))
  (set! qdata⊤ (normalizeq⊤
                qdata-start
                (+ 4 ;; qdata^ #t #f '()
                   num-number num-string num-symbol num-char num-qvector)))
  (set! conditionally-qdata⊤ize (mk-conditionally-⊤ize qdata-start qdata⊤))
  ;; Dynamic ivector⊤ subsumes qvector⊤
  (set! kill-ivectors
        (for/fold ([kill-ivectors kill-ivectors])
            ([i (in-range qvector-start ivector⊤-pos)])
          (add-to-mask kill-ivectors (arithmetic-shift 1 i))))
  ;; Dynamic cons⊤ subsumes qcons⊤
  (set! kill-conses (add-to-mask kill-conses (arithmetic-shift 1 qcons-pos)))
  (define vector⊤-pos (+ 1 ivector⊤-pos))
  (define cons⊤-pos (+ 2 ivector⊤-pos))
  ;; Set bits for all the top elements to later check for lattice jumps
  (set! top-mask
        (for/fold ([acc 0])
            ([n (list number-start string-start symbol-start char-start
                      qvector-start ivector⊤-pos
                      vector⊤-pos cons⊤-pos)])
          (bitwise-ior acc (arithmetic-shift 1 n))))
  (set! ivector⊤-bv (arithmetic-shift 1 ivector⊤-pos))
  (set! vector⊤-bv (arithmetic-shift 1 vector⊤-pos))
  (set! cons⊤-bv (arithmetic-shift 1 cons⊤-pos))
  (set! conditionally-ivector⊤ize (mk-conditionally-⊤ize ivector⊤-pos ivector⊤))
  (set! conditionally-vector⊤ize (mk-conditionally-⊤ize vector⊤-pos vector⊤))
  (set! conditionally-cons⊤ize (mk-conditionally-⊤ize cons⊤-pos cons⊤))
  (init-bit/value!
   (append starting-values number-range string-range symbol-range char-range
           qvector-range ;; will be extended, thus the interval will be coarse.
           ;; The following top elements are not covered by qdata, and in some cases
           ;; they cover part of qdata (like qcons^ qvector^ and all immutable vector literals)
           (list vector-immutable^ vector^ cons^))))

;; For all top elements e, if e set in dv-tst, enormalize bv-dst.
(define (conditionally-⊤ize bv-dst bv-tst)
  (let* ([bv-dst
          (cond
           [(bitwise-bit-set? bv-tst qdata-start)
            (qdata⊤ bv-dst)]
           [else
            (let* ([bv-dst (conditionally-number⊤ize bv-dst)]
                   [bv-dst (conditionally-string⊤ize bv-dst)]
                   [bv-dst (conditionally-symbol⊤ize bv-dst)]
                   [bv-dst (conditionally-char⊤ize bv-dst)]
                   [bv-dst (conditionally-qvector⊤ize bv-dst)])
              bv-dst)])]
         [bv-dst (conditionally-ivector⊤ize bv-dst)]
         [bv-dst (conditionally-vector⊤ize bv-dst)]
         [bv-dst (conditionally-cons⊤ize bv-dst)])
    bv-dst))

;; Set
(define (add-to-mask mask bit) (bitwise-and mask (bitwise-not bit)))
(define (αbv-rem1 abv v)
  (match-define (αbv start extent bv) abv)
  (αbv start extent (add-to-mask bv (value->αbv v))))
(define (value->αbv v)
  (hash-ref! value-register v
             (λ ()
                (define num (hash-count value-register))
                (define new-bit (arithmetic-shift 1 num))
                (define-syntax-rule (ext-mask id) (set! id (add-to-mask id new-bit)))
                (cond
                 [(vectorv-immutable? v) (ext-mask kill-ivectors)]
                 [(vectorv? v) (ext-mask kill-vectors)]
                 [(consv? v) (ext-mask kill-conses)]
                 [else (void)])
                (when (>= num (vector-length bit-register))
                  (grow-bit-register))
                (vector-set! bit-register num v)
                (αbv new-bit 1 new-bit))))

;; Consider bv1 to be "new" and thus if it contains any tops,
;; we kill all values under them in the join.
(define (join αbv0 αbv1)
  (match* (αbv0 αbv1)
    [((αbv s0 e0 bv0) (αbv s1 e1 bv1))
     (define s* (min s0 s1))
     (define e* (- (max (+ s0 e0) (+ s1 e1)) s*))
     (define union (bitwise-ior bv0 bv1))
     (αbv s* e*
          ;; The slow path is only hit if bv1 has top values.
          (if (exact-zero? (bitwise-and top-mask bv1))
              union
              (let* ([union (qdata⊤ union)]
                     [union (number⊤ union)]
                     [union (string⊤ union)]
                     [union (symbol⊤ union)]
                     [union (char⊤ union)]
                     [union (qvector⊤ union)]
                     [union (vector⊤ union)]
                     [union (cons⊤ union)])
                union)))]
    [(#f αbv1) αbv1]
    [(αbv0 #f) αbv0]))

;; Make top values clobber concrete values to decrease irrelevant flows.
(define (join1 αbv val) (join αbv (value->αbv val)))

;; INVARIANT: expect top values to clobber all lesser values in compared sets
;; bv0 ⊑ bv1 iff empty?(bv0 - bv1) iff empty?(bv0 ∩ bv1^C)
(define/match (bv-⊑? αbv0 αbv1)
  [((αbv s0 e0 bv0) (αbv s1 e1 bv1))
   ;; If the abstract intervals don't intersect, they absolutely can't
   ;; be subsets.
   (and (or (= s0 s1)
           (and (< s0 s1) (>= (+ s0 e0) s1))
           (and (< s1 s0) (>= (+ s1 e1) s0)))
        ;; To make 1 ⊑ number⊤, we promote numbers in bv0 to number⊤
        ;; only if bv1 contains number⊤, making the number ⊑ test succeed.
        ;; So forth for other ⊤ elements.
        (let ([bv0 (conditionally-⊤ize bv0 bv1)])
          (exact-zero? (bitwise-and bv0 (bitwise-not bv1)))))]
  [(#f _) #t]
  [(_ #f) #f])

;; TODO: To have a faster next-bit check, we can subdivide
;; the bitvector into chunks of 62, 31, 16 and 8 bits given the
;; sparseness of the set, and use faster fixnum operations and
;; skip known useless iterations over several zeroes.
;; For now, do the naive thing.
(define/match (bv-first-bit bv)
  [((αbv start extent bv))
   (cond [(exact-zero? bv) (values #f 0)]
         [else
          (define bv* (arithmetic-shift bv (- start)))
          (orig-bv-first-bit start bv*)])]
  [(#f) (values #f 0)])

(define (bv-next-bit-seq pos)
  (define idx (unsafe-struct-ref pos 0))
  (define bv (quotient (unsafe-struct-ref pos 1) 2))
  (if (exact-zero? bv)
      (bv-seq #f 0)
      (let-values ([(idx bv) (orig-bv-first-bit idx bv)])
        (bv-seq idx bv))))

(struct bv-seq (idx bv*) #:prefab)

(define (in-bv->values bv)
  (make-do-sequence
   (λ ()
      (values (λ (pos) (vector-ref bit-register (bv-seq-idx pos)))
              bv-next-bit-seq
              (let-values ([(idx bv*) (bv-first-bit bv)])
                (bv-seq idx bv*))
              bv-seq-idx #f #f))))

(define-sequence-syntax *in-bv->values
  (λ () #'in-bv->values)
  (λ (stx)
     (syntax-parse stx #:literals (singleton value->αbv)
       [[(id) (_ ((~or singleton value->αbv) v))]
        #'[(id) (:do-in ([(id) v]) #t () #t () #t #f ())]]
       [[(id) (_ αbv-expr)]
        #'[(id)
           (:do-in
            ([(idx bv) (bv-first-bit αbv-expr)])
            (void)
            ([bv bv]
             [idx idx])
            idx
            ([(idx* bv*) (orig-bv-first-bit idx bv)]
             [(id) (vector-ref bit-register idx)])
            #t
            #t
            (bv* idx*))]]
       [_ #f])))

(define-syntax-rule (with-bitvector-data/intervals . body)
  (splicing-syntax-parameterize
      ([nothing (make-rename-transformer #'bv-nothing)]
       [is-nothing? (make-rename-transformer #'αbv-is-nothing?)]
       [singleton (make-rename-transformer #'value->αbv)]
       [abstract-values? (make-rename-transformer #'αbv?)]
       [⊓ (make-rename-transformer #'join)]
       [⊓1 (make-rename-transformer #'join1)]
       [rem1 (make-rename-transformer #'αbv-rem1)]
       [⊑? (make-rename-transformer #'bv-⊑?)]
       [≡ (make-rename-transformer #'αbv-≡)]
       [in-abstract-values (make-rename-transformer #'*in-bv->values)]
       [snull (make-rename-transformer #'bv-snull)]
       [interval-abstraction (make-rename-transformer #'αbv-interval)]
       [init-sequence (list*
                       #'(reset-registers!)
                       (syntax-parameter-value #'init-sequence))]
       [register-datum (make-rename-transformer #'bv-register-datum!)])
    . body))
