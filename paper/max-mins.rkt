#lang racket
(require "proctime.rkt")

(define (vector-avg v)
  (define t (vector-filter (negate (λ (x) (eq? x 'unset))) v))
  (if (zero? (vector-length t))
      +inf.0
      (/ (for/sum ([x (in-vector t)]) x)
         (vector-length t))))
    
(define (pick-min alg-pairs)
  (argmin (λ (p) (second p)) alg-pairs))

(define (pick-max alg-pairs)
  (argmax (λ (p) (second p)) alg-pairs))

(define max-mins
  (for/list ([(name report) (in-hash timings)])
    (define ls (for/list ([(alg ns) (in-hash report)])
                 (list alg (vector-avg (numbers-run ns)))))
    (cons name 
          (list (pick-min ls)
                (pick-max ls)))))

(define speedups
  (map (λ (l)
         (match l
           [(cons name (list (list _ min-time) (list _ max-time)))
            (define bounded-maxt (min max-time (* 30 60 1000)))
            (list name (/ max-time min-time) (/ bounded-maxt min-time))]))
       max-mins))
