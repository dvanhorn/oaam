#lang racket/base
(require math/number-theory racket/dict racket/match racket/set
         racket/generic
         racket/bool
         (for-syntax racket/base syntax/parse racket/syntax)
         racket/trace)
(provide GH? GH-gh
         GH-hash-add GH-hash-union GH-hash? for/GH-hash for*/GH-hash empty-GH-hash
         GH-set? GH-set₀ GH-singleton-set for/GH-set for*/GH-set
         init-GH!
         ;; For testing purposes only
         GHT-hash-add GHT-hash-union GHT-hash? for/GHT-hash for*/GHT-hash empty-GHT-hash
         GHT-set? GHT-set₀ GHT-singleton-set for/GHT-set for*/GHT-set)

(struct -unmapped ()) (define unmapped (-unmapped))

(define element-hash #f)
(define gh-cache #f)
(define current-prime #f)
(define (next-prime!)
  (begin0 current-prime
    (set! current-prime (next-prime current-prime))))
;; Can't be weak hashes because equal sets can be given different primes
(define (init-GH!)
  (set! element-hash (make-hash))
  (set! gh-cache (make-hash))
  (set! current-prime 2))

;; injection ℕ² → ℕ
;; C₂+(x, y) = Σ[0..x] + Σ[x+2..y+2]
(define (C₂ x y)
  (define initial (* 1/2 x (+ x 1)))
  (if (> x y)
      initial
      (+ initial (* 1/2 (+ y 2) (+ y 3)) (* -1/2 (+ x 1) (+ x 2)))))

(define (P v)
  (match v
    [(GH gh) gh]
    [_
     (match (hash-ref gh-cache v unmapped)
       [(== unmapped eq?)
        (define res
          (match v
            [(? set? vs) (for/product ([v (in-set vs)]) (P v))]
            [(? dict? m) (for/product ([(k v) (in-dict m)])
                           (C₂ (P k) (P v)))]
            [_ (hash-ref! element-hash v next-prime!)]))
        (hash-set! gh-cache v res)
        res]
       [gh gh])]))

(define ((bad-key k)) (error 'dict-ref "Unmapped key ~a" k))

(struct GH (gh)
        #:methods gen:equal+hash
        [(define (equal-proc x y rec)
           (match* (x y)
             [((GH ghx) (GH ghy)) (= ghx ghy)]
             [(_ _) #f]))
         (define (hash-proc x rec) (rec (GH-gh x)))
         (define (hash2-proc x rec) (rec (GH-gh x)))])

;; XXX: Assumes each iteration produces unique keys
(define-syntax (for/hash-acc stx)
  (syntax-case stx ()
    [(_ folder hash-name clauses body ...)
     (quasisyntax/loc stx
       (let-values
           ([(gh h)
             (folder #,stx
                     ([gh 1] [h (hash)])
                     clauses
                     (define-values (k v) (let () body ...))
                     (values (* gh (C₂ (P k) (P v)))
                             (hash-set h k v)))])
         (hash-name gh h)))]))

;; Does not assume values produced are unique.
(define-syntax (for/set-acc stx)
  (syntax-case stx ()
    [(_ folder set-name clauses body ...)
     (quasisyntax/loc stx
       (let-values
           ([(gh s)
             (folder #,stx
                     ([gh 1] [s (set)])
                     clauses
                     (define v (let () body ...))
                     (define Pv (P v))
                     (if (eq? 0 (remainder gh Pv))
                         (values gh s)
                         (values (* gh (P v))
                                 (set-add s v))))])
         (set-name gh s)))]))

(define-syntax (mk-GH-set/hash stx)
  (syntax-parse stx
    [(_ (~or (~once (~seq #:set-names set-name empty-set-name singleton-set-name for/set-name for*/set-name))
             (~once (~seq #:hash-names hash-name empty-hash-name hash-add-name hash-union-name for/hash-name for*/hash-name)))
        ...
        (~bind [set-name-s (format-id #'set-name "~a-s" #'set-name)]
               [hash-name-h (format-id #'hash-name "~a-h" #'hash-name)])
        (~optional
              (~and #:eqs (~bind [(set-eq 1)
                                  (list
                                   #'#:methods #'gen:equal+hash
                                   #'[(define (equal-proc x y rec)
                                        (match* (x y)
                                          [((set-name ghx sx) (set-name ghy sy))
                                           (define res (= ghx ghy))
                                           #;
                                           (when (xor res (equal? sx sy))
                                             (error 'goedel-set "Not injective ~a ~a ~a ~a ~a" ghx ghy sx sy element-hash))
                                           res]
                                          [(_ _) #f]))
                                      (define (hash-proc x rec) (rec (set-name-s x)))
                                      (define (hash2-proc x rec) (rec (set-name-s x)))])]
                                 [(hash-eq 1)
                                  (list
                                   #'#:methods #'gen:equal+hash
                                   #'[(define (equal-proc x y rec)
                                        (match* (x y)
                                          [((hash-name ghx hx) (hash-name ghy hy))
                                           (define res (= ghx ghy))
                                           #;
                                           (when (xor res (equal? hx hy))
                                             (error 'goedel-hash "Not injective ~a ~a ~a ~a ~a" ghx ghy hx hy element-hash))
                                           res]
                                          [(_ _) #f]))
                                      (define (hash-proc x rec) (rec (hash-name-h x)))
                                      (define (hash2-proc x rec) (rec (hash-name-h x)))])]))
              #:defaults ([(set-eq 1) '()] [(hash-eq 1) '()])))
     (syntax/loc stx
      (begin
        (struct set-name GH (s) #:transparent
                set-eq ...
                #:methods gen:set
                [(define (set-empty? g) (= 1 (GH-gh g)))
                 (define (set-member? g x) (eq? 0 (remainder (GH-gh g) (P x))))
                 (define (set-count g) (set-count (set-name-s g)))
                 (define/match (set=? s0 s1) [((GH ghx) (GH ghy)) (= ghx ghy)])
                 (define/match (subset? s0 s1)
                   [((GH ghx) (GH ghy)) (eq? 0 (remainder ghy ghx))])
                 (define/match (proper-subset? s0 s1)
                   [((GH ghx) (GH ghy)) (and (not (= ghx ghy))
                                             (eq? 0 (remainder ghy ghx)))])
                 (define/generic gset-map set-map)
                 (define (set-map s f) (gset-map (set-name-s s) f))
                 (define/generic gset-for-each set-for-each)
                 (define (set-for-each s f) (gset-for-each (set-name-s s) f))
                 (define/generic gin-set in-set)
                 (define (in-set s) (gin-set (set-name-s s)))
                 (define/generic gset->list set->list)
                 (define (set->list s) (gset->list (set-name-s s)))
                 (define/generic gset->stream set->stream)
                 (define (set->stream s) (gset->stream (set-name-s s)))
                 (define/generic gset-first set-first)
                 (define (set-first s) (gset-first (set-name-s s)))
                 (define/generic gset-rest set-rest)
                 (define/match (set-rest s)
                   [((set-name gh s))
                    (define sf (gset-first s))
                    (set-name (quotient gh (P sf))
                              (gset-rest s))])
                 (define/generic gset-add set-add)
                 (define/match (set-add gs v)
                   [((set-name gh s) _)
                    (define Pv (P v))
                    (if (eq? 0 (remainder gh Pv))
                        gs
                        (set-name (* gh Pv) (gset-add s v)))])
                 (define/generic gset-remove set-remove)
                 (define/match (set-remove gs v)
                   [((set-name gh s) _)
                    (define Pv (P v))
                    (if (eq? 0 (remainder gh Pv))
                        (set-name (quotient gh Pv) (gset-remove s v))
                        gs)])
                 (define/generic gset-copy set-copy)
                 (define/match (set-copy gs)
                   [((set-name gh s)) (set-name gh (gset-copy s))])
                 (define (set-clear gs) empty-set-name)
                 (define/generic gset-union set-union)

                 (define/match (bin-union gs0 gs1)
                   [((set-name gh0 s0) (set-name gh1 s1))
                    (define ghu (lcm gh0 gh1))
                    (cond
                     [(= ghu gh0) gs0]
                     [(= ghu gh1) gs1]
                     [else (set-name ghu (gset-union s0 s1))])])

                 (define (set-union gs0 . gsets)
                   (for/fold ([gs gs0]) ([gsi (in-list gsets)])
                     (bin-union gs gsi)))

                 (define/generic gset-intersect set-intersect)

                 (define/match (bin-intersect gs0 gs1)
                   [((set-name gh0 s0) (set-name gh1 s1))
                    (define ghi (gcd gh0 gh1))
                    (cond
                     [(= ghi gh0) gs0]
                     [(= ghi gh1) gs1]
                     [else (set-name ghi (gset-intersect s0 s1))])])

                 (define (set-intersect gs0 . gsets)
                   (for/fold ([gs gs0]) ([gsi (in-list gsets)])
                     (bin-intersect gs gsi)))

                 (define/generic gset-subtract set-subtract)
                 (define/match (bin-subtract gs0 gs1)
                   [((set-name gh0 s0) (set-name gh1 s1))
                    (define ghi (gcd gh0 gh1))
                    (if (= 1 ghi)
                        gs0
                        (set-name (quotient gh0 ghi) (gset-subtract s0 s1)))])
                 (define (set-subtract gs0 . gsets)
                   (for/fold ([gs gs0]) ([gsi (in-list gsets)])
                     (bin-subtract gs gsi)))

                 (define (set-symmetric-difference gs0 . gsets)
                   (error 'set-symmetric-difference "TODO for Gödel hashing"))])

        (struct hash-name GH (h) #:transparent
                hash-eq ...
                #:methods gen:dict
                [(define (dict-ref lh k [default (bad-key k)])
                   (hash-ref (hash-name-h lh) k default))
                 (define (dict-set lh k v)
                   (match lh
                     [(hash-name gh h)
                      (define prev (hash-ref h k unmapped))
                      (define Pk (P k))
                      (define gh* (if (eq? prev unmapped) gh (quotient gh (C₂ Pk (P prev)))))
                      (hash-name (* gh* (C₂ Pk (P v))) (hash-set h k v))]))
                 (define (dict-remove lh k)
                   (match lh
                     [(hash-name gh h)
                      (define kv (hash-ref lh k unmapped))
                      (if (eq? kv unmapped)
                          lh
                          (hash-name (quotient gh (C₂ (P k) (P kv))) (hash-remove h k)))]))
                 (define (dict-count lh) (hash-count (hash-name-h lh)))
                 (define (dict-iterate-first lh) (hash-iterate-first (hash-name-h lh)))
                 (define (dict-iterate-next lh itr) (hash-iterate-next (hash-name-h lh) itr))
                 (define (dict-iterate-key lh itr) (hash-iterate-key (hash-name-h lh) itr))
                 (define (dict-iterate-value lh itr) (hash-iterate-value (hash-name-h lh) itr))])

        (define empty-hash-name (hash-name 1 #hash()))
        (define empty-set-name (set-name 1 (set)))
        (define (singleton-set-name v) (set-name (P v) (set v)))

        (define-syntax-rule (define-GH-op name mk-set set-op)
          (define (name h* k v)
            (match h*
              [(hash-name gh h)
               (define Pk (P k))
               (define Pv (P v))
               (match (hash-ref h k unmapped)
                 [(== unmapped eq?) (hash-name (* gh (C₂ Pk Pv)) (hash-set h k (mk-set v)))]
                 [vs (define Pvs (P vs))
                     (cond
                      [(eq? 0 (remainder Pvs Pv)) h*]
                      [else
                       (hash-name (* (quotient gh (C₂ Pk Pvs))
                                     (C₂ Pk (* Pvs (P v))))
                                  (hash-set h k (set-op vs v)))])])])))
        (define-GH-op hash-add-name set set-add)
        (define-GH-op hash-union-name values set-union)

        (define-syntax-rule (for/hash-name . in) (for/hash-acc for/fold/derived hash-name . in))
        (define-syntax-rule (for*/hash-name . in) (for/hash-acc for*/fold/derived hash-name . in))
        (define-syntax-rule (for/set-name . in) (for/set-acc for/fold/derived set-name . in))
        (define-syntax-rule (for*/set-name . in) (for/set-acc for*/fold/derived set-name . in))))]))
(mk-GH-set/hash #:set-names GH-set GH-set₀ GH-singleton-set for/GH-set for*/GH-set
                #:hash-names GH-hash empty-GH-hash GH-hash-add GH-hash-union for/GH-hash for*/GH-hash
                #:eqs)
(mk-GH-set/hash #:set-names GHT-set GHT-set₀ GHT-singleton-set for/GHT-set for*/GHT-set
                #:hash-names GHT-hash empty-GHT-hash GHT-hash-add GHT-hash-union for/GHT-hash for*/GHT-hash)
