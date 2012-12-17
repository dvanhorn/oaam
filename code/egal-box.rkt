#lang racket/base

(provide ebox
         (rename-out [set-ebox-datum! set-ebox!]
                     [ebox-datum eunbox]))

(struct ebox (datum) #:mutable #:transparent
        #:methods gen:equal+hash
        [(define (equal-proc x y _) (eq? x y))
         (define (hash-proc ebox:struct _) (eq-hash-code ebox:struct))
         (define hash2-proc hash-proc)])
#;
(module+ stress-test
  (struct ebox2 (datum) #:mutable)
  (define (stress cons get N)
    (define h (make-hash))
    (for ([i (in-range 0 N)])
      (hash-set! h i (cons (random (add1 i)))))
    (for/fold ([the-last #f]) ([i (in-range 1 N)])
      (get (hash-ref h (random i)))))

  (define runs 3000000)
  (define-values (reals reals2)
    (for/lists (reals reals2) ([x 4])
      (define-values (_ cpu real gc) (time-apply stress (list ebox ebox-datum runs)))
      (define-values (_2 cpu2 real2 gc2) (time-apply stress (list ebox2 ebox2-datum runs)))
      (values real real2)))
  (define (average lst) (exact->inexact (/ (apply + lst) (length lst))))
  (average reals)
  (average reals2))
