#lang racket/base
(require math/number-theory racket/dict racket/match racket/set
         (for-syntax racket/base))
(provide empty-GH GH-gh init-GH! GH? for/GH-hash)

(struct -unmapped ()) (define unmapped (-unmapped))

(define element-hash #f)
(define current-prime #f)
(define (next-prime!)
  (begin0 current-prime
    (set! current-prime (next-prime current-prime))))
(define (init-GH!)
  (set! element-hash (make-hash))
  (set! current-prime 2))

;; All I need for now.
(define (P v)
  (match v
   [(? set-immutable? vs) (for/product ([v (in-set vs)]) (P v))]
   [(? dict? m) (for/product ([(k v) (in-dict m)])
                  (C₂ (P k) (P v)))]
   [_ (hash-ref! element-hash v next-prime!)]))

(define ((bad-key k)) (error 'dict-ref "Unmapped key ~a" k))
(struct GH (h gh)
        #:methods gen:equal+hash
        [(define (equal-proc x y rec)
           (match* (x y)
             [((GH _ ghx) (GH _ ghy)) (= ghx ghy)]
             [(_ _) #f]))
         (define (hash-proc x rec) (rec (GH-h x)))
         (define (hash2-proc x rec) (rec (GH-h x)))]
        #:methods gen:dict
        [(define (dict-ref lh k [default (bad-key k)])
           (hash-ref (GH-h lh) k default))
         (define (dict-set lh k v)
           (match lh
             [(GH h gh)
              (define prev (hash-ref h k unmapped))
              (define Pk (P k))
              (define gh* (if (eq? prev unmapped) gh (quotient gh (C₂ Pk (P prev)))))
              (GH (hash-set h k v) (* gh* (C₂ Pk (P v))))]))
         (define (dict-remove lh k)
           (match lh
             [(GH h gh)
              (define kv (hash-ref lh k unmapped))
              (if (eq? kv unmapped)
                  lh
                  (GH (hash-remove h k) (quotient gh (C₂ (P k) (P kv)))))]))
         (define (dict-count lh) (hash-count (GH-h lh)))
         (define (dict-iterate-first lh) (hash-iterate-first (GH-h lh)))
         (define (dict-iterate-next lh itr) (hash-iterate-next (GH-h lh) itr))
         (define (dict-iterate-key lh itr) (hash-iterate-key (GH-h lh) itr))
         (define (dict-iterate-value lh itr) (hash-iterate-value (GH-h lh) itr))])
(define empty-GH (GH #hash() 1))

(define-syntax (for/GH-hash stx)
  (syntax-case stx ()
    [(_ clauses body ...)
     (quasisyntax/loc stx
       (let-values
           ([(h gh)
             (for/fold/derived #,stx
                               ([h (hash)] [gh 1])
                               clauses
                               (define-values (k v) (let () body ...))
                               (values (hash-set h k v)
                                       (* gh (C₂ (P k) (P v)))))])
         (GH h gh)))]))

;; injection ℕ² → ℕ
;; C₂+(x, y) = Σ[0..x] + Σ[x+2..y+2]
(define (C₂ x y)
  (define initial (* 1/2 x (+ x 1)))
  (if (> x y)
      initial
      (+ initial (* 1/2 (+ y 2) (+ y 3)) (* -1/2 (+ x 1) (+ x 2)))))
