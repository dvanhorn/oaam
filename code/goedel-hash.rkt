#lang racket/base
(require math/number-theory racket/dict racket/match racket/set
         racket/generic
         (for-syntax racket/base)
         racket/trace)
(provide GH? GH-gh
         GH-hash-add GH-hash-union GH-hash? for/GH-hash empty-GH-hash
         GH-set? GH-set₀ GH-singleton-set for/GH-set
         init-GH!
         (rename-out [*in-GH-set in-GH-set]))

(struct -unmapped ()) (define unmapped (-unmapped))

(define element-hash #f)
(define gh-cache #f)
(define current-prime #f)
(define (next-prime!)
  (begin0 current-prime
    (set! current-prime (next-prime current-prime))))
(define (init-GH!)
  (set! element-hash (make-hash))
  (set! gh-cache (make-hash))
  (set! current-prime 2))

(define (P v)
  (match v
    [(GH gh) gh]
    [_
     (match (hash-ref gh-cache v unmapped)
       [(== unmapped eq?)
        (define res
          (match v
            [(? set-immutable? vs) (for/product ([v (in-set vs)]) (P v))]
            [(? dict? m) (for/product ([(k v) (in-dict m)])
                           (C₂ (P k) (P v)))]
            [_ (hash-ref! element-hash v next-prime!)]))
        (hash-set! gh-cache v res)
        res]
       [gh gh])]))

(define-syntax-rule (define-GH-op name mk-set set-op)
 (define (name h* k v)
   (match h*
     [(GH-hash gh h)
      (define Pk (P k))
      (define Pv (P v))
      (match (hash-ref h k unmapped)
        [(== unmapped eq?) (GH-hash (* gh (C₂ Pk Pv)) (hash-set h k (mk-set v)))]
        [vs (define Pvs (P vs))
            (cond
             [(eq? 0 (remainder Pvs Pv)) h*]
             [else
              (GH-hash (* (quotient gh (C₂ Pk Pvs))
                          (C₂ Pk (* Pvs (P v))))
                       (hash-set h k (set-op vs v)))])])])))
(define-GH-op GH-hash-add set set-add)
(define-GH-op GH-hash-union values set-union)

(define ((bad-key k)) (error 'dict-ref "Unmapped key ~a" k))
(struct GH (gh)
        #:methods gen:equal+hash
        [(define (equal-proc x y rec)
           (match* (x y)
             [((GH ghx) (GH ghy)) (= ghx ghy)]
             [(_ _) #f]))
         (define (hash-proc x rec) (rec (GH-gh x)))
         (define (hash2-proc x rec) (rec (GH-gh x)))])
(struct GH-set GH (s)
        #:methods gen:equal+hash
        [(define (equal-proc x y rec)
           (match* (x y)
             [((GH-set ghx _) (GH-set ghy _)) (= ghx ghy)]
             [(_ _) #f]))
         (define (hash-proc x rec) (rec (GH-set-s x)))
         (define (hash2-proc x rec) (rec (GH-set-s x)))]
        #:methods gen:set
        [(define (set-empty? g) (= 1 (GH-gh g)))
         (define (set-member? g x) (eq? 0 (remainder (GH-gh g) (P x))))
         (define (set-count g) (set-count (GH-set-s g)))
         (define/match (set=? s0 s1) [((GH ghx) (GH ghy)) (= ghx ghy)])
         (define/match (subset? s0 s1)
           [((GH ghx) (GH ghy)) (eq? 0 (remainder ghy ghx))])
         (define/match (proper-subset? s0 s1)
           [((GH ghx) (GH ghy)) (and (not (= ghx ghy))
                                     (eq? 0 (remainder ghy ghx)))])
         (define/generic gset-map set-map)
         (define (set-map s f) (gset-map (GH-set-s s) f))
         (define/generic gset-for-each set-for-each)
         (define (set-for-each s f) (gset-for-each (GH-set-s s) f))
         (define/generic gin-set in-set)
         (define (in-set s) (gin-set (GH-set-s s)))
         (define/generic gset->list set->list)
         (define (set->list s) (gset->list (GH-set-s s)))
         (define/generic gset->stream set->stream)
         (define (set->stream s) (gset->stream (GH-set-s s)))
         (define/generic gset-first set-first)
         (define (set-first s) (gset-first (GH-set-s s)))
         (define/generic gset-rest set-rest)
         (define/match (set-rest s)
           [((GH-set gh s))
              (define sf (gset-first s))
              (GH-set (quotient gh (P sf))
                      (gset-rest s))])
         (define/generic gset-add set-add)
         (define/match (set-add gs v)
           [((GH-set gh s) _)
            (define Pv (P v))
            (if (eq? 0 (remainder gh Pv))
                gs
                (GH-set (* gh Pv) (gset-add s v)))])
         (define/generic gset-remove set-remove)
         (define/match (set-remove gs v)
           [((GH-set gh s) _)
            (define Pv (P v))
            (if (eq? 0 (remainder gh Pv))
                (GH-set (quotient gh Pv) (gset-remove s v))
                gs)])
         (define/generic gset-copy set-copy)
         (define/match (set-copy gs)
           [((GH-set gh s)) (GH-set gh (gset-copy s))])
         (define (set-clear gs) GH-set₀)
         (define/generic gset-union set-union)
         
         (define/match (bin-union gs0 gs1)
           [((GH-set gh0 s0) (GH-set gh1 s1))
            (define ghu (lcm gh0 gh1))
            (cond
             [(= ghu gh0) gs0]
             [(= ghu gh1) gs1]
             [else (GH-set ghu (gset-union s0 s1))])])
         
         (define (set-union gs0 . gsets)
           (for/fold ([gs gs0]) ([gsi (in-list gsets)])
             (bin-union gs gsi)))
         
         (define/generic gset-intersect set-intersect)
         
         (define/match (bin-intersect gs0 gs1)
           [((GH-set gh0 s0) (GH-set gh1 s1))
            (define ghi (gcd gh0 gh1))
            (cond
             [(= ghi gh0) gs0]
             [(= ghi gh1) gs1]
             [else (GH-set ghi (gset-intersect s0 s1))])])
         
         (define (set-intersect gs0 . gsets)
           (for/fold ([gs gs0]) ([gsi (in-list gsets)])
             (bin-intersect gs gsi)))
         
         (define/generic gset-subtract set-subtract)
         (define/match (bin-subtract gs0 gs1)
           [((GH-set gh0 s0) (GH-set gh1 s1))
            (define ghi (gcd gh0 gh1))
            (if (= 1 ghi)
                gs0
                (GH-set (quotient gh0 ghi) (gset-subtract s0 s1)))])
         (define (set-subtract gs0 . gsets)
           (for/fold ([gs gs0]) ([gsi (in-list gsets)])
             (bin-subtract gs gsi)))
         
         (define (set-symmetric-difference gs0 . gsets)
            (error 'set-symmetric-difference "TODO for Gödel hashing"))])

(define (GH-singleton-set v) (GH-set (P v) (set v)))

(define GH-set₀ (GH-set 1 (set)))
(struct GH-hash GH (h)
        #:methods gen:equal+hash
        [(define (equal-proc x y rec)
           (match* (x y)
             [((GH-hash ghx _) (GH-hash ghy _)) (= ghx ghy)]
             [(_ _) #f]))
         (define (hash-proc x rec) (rec (GH-hash-h x)))
         (define (hash2-proc x rec) (rec (GH-hash-h x)))]
        #:methods gen:dict
        [(define (dict-ref lh k [default (bad-key k)])
           (hash-ref (GH-hash-h lh) k default))
         (define (dict-set lh k v)
           (match lh
             [(GH-hash gh h)
              (define prev (hash-ref h k unmapped))
              (define Pk (P k))
              (define gh* (if (eq? prev unmapped) gh (quotient gh (C₂ Pk (P prev)))))
              (GH-hash (* gh* (C₂ Pk (P v))) (hash-set h k v))]))
         (define (dict-remove lh k)
           (match lh
             [(GH-hash gh h)
              (define kv (hash-ref lh k unmapped))
              (if (eq? kv unmapped)
                  lh
                  (GH-hash (quotient gh (C₂ (P k) (P kv))) (hash-remove h k)))]))
         (define (dict-count lh) (hash-count (GH-hash-h lh)))
         (define (dict-iterate-first lh) (hash-iterate-first (GH-hash-h lh)))
         (define (dict-iterate-next lh itr) (hash-iterate-next (GH-hash-h lh) itr))
         (define (dict-iterate-key lh itr) (hash-iterate-key (GH-hash-h lh) itr))
         (define (dict-iterate-value lh itr) (hash-iterate-value (GH-hash-h lh) itr))])
(define (in-GH-set s) (custom-in-set (GH-set-s s)))
(define-sequence-syntax *in-GH-set
  (λ () #'in-GH-set)
  (λ (stx)
     (syntax-case stx ()
       [[(x) (_ e)]
        #'[(x) (in-set (GH-set-s e))]]
       [_ #f])))
(define empty-GH-hash (GH-hash 1 #hash()))

;; XXX: Assumes each iteration produces unique keys
(define-syntax (for/GH-hash stx)
  (syntax-case stx ()
    [(_ clauses body ...)
     (quasisyntax/loc stx
       (let-values
           ([(gh h)
             (for/fold/derived #,stx
                               ([gh 1] [h (hash)])
                               clauses
                               (define-values (k v) (let () body ...))
                               (values (* gh (C₂ (P k) (P v)))
                                       (hash-set h k v)))])
         (GH-hash gh h)))]))

;; Does not assume values produced are unique.
(define-syntax (for/GH-set stx)
  (syntax-case stx ()
    [(_ clauses body ...)
     (quasisyntax/loc stx
       (let-values
           ([(gh s)
             (for/fold/derived #,stx
                               ([gh 1] [s (set)])
                               clauses
                               (define v (let () body ...))
                               (define Pv (P v))
                               (if (eq? 0 (remainder gh Pv))
                                   (values gh s)
                                   (values (* gh (P v))
                                           (set-add s v))))])
         (GH-set gh s)))]))

;; injection ℕ² → ℕ
;; C₂+(x, y) = Σ[0..x] + Σ[x+2..y+2]
(define (C₂ x y)
  (define initial (* 1/2 x (+ x 1)))
  (if (> x y)
      initial
      (+ initial (* 1/2 (+ y 2) (+ y 3)) (* -1/2 (+ x 1) (+ x 2)))))