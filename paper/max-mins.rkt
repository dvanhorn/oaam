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



(define algo-name
  '(#;("bl" . "baseline")
    ("sp" . "baseline") ;; Specialized is the new baseline
    ("ls" . "lazy")
    ("lc" . "compiled")
    ("ld" . "functional deltas")
    #;("ia" . "imperative accumulated deltas")
    ("id" . "imperative deltas")
    #;("pa" . "preallocated accumulated deltas")
    ("pd" . "preallocated deltas")
    #;("it" . "imperative timestamp")
    #;("pt" . "preallocated timestamp")))

(define baseline-time
  (vector-avg (numbers-run (hash-ref (hash-ref timings "church") "sp"))))

(define baseline-mem
  (vector-avg (numbers-peak-mem (hash-ref (hash-ref timings "church") "sp"))))

(define baseline-rate
  (vector-avg (numbers-state-rate (hash-ref (hash-ref timings "church") "sp"))))

(define ct (hash-ref timings "church"))

(for/list ([(alg nums) (in-hash (hash-ref timings "church"))]
           #:unless (string=? alg "bl"))
  (list alg (/ baseline-time (vector-avg (numbers-run nums)))))


(require unstable/sequence)

(define rel-time-data
  (for/list ([(key desc) (in-pairs algo-name)]
             [n (in-naturals)])
    (vector n #;key #;desc (/ baseline-time 
                              (vector-avg (numbers-run (hash-ref ct key)))))))
 
(define rel-mem-data
  (for/list ([(key desc) (in-pairs algo-name)]
             [n (in-naturals)])
    (vector n #;key #;desc (/ baseline-mem 
                              (vector-avg (numbers-peak-mem (hash-ref ct key)))))))
 

(define rel-states-per-sec-data
  (for/list ([(key desc) (in-pairs algo-name)]
             [n (in-naturals)])
    (vector n #;key #;desc (/ (vector-avg (numbers-state-rate (hash-ref ct key)))
                              baseline-rate))))
 

(require plot)
(define data
  (list #(0 0) #(15 0.6) #(30 9.5) #(45 10.0) #(60 16.6)
            #(75 41.6) #(90 42.7) #(105 65.5) #(120 78.9)
            #(135 78.9) #(150 131.1) #(165 151.1) #(180 176.2)))
(plot (list
       (lines rel-time-data #:color 2 #:width 2 #:label "Speedup")
       (points rel-time-data #:color 1 #:line-width 2)
       #;(lines rel-mem-data #:color 4 #:width 2 #:label "Memory")
       #;(points rel-mem-data #:color 3 #:line-width 2)
       (lines rel-states-per-sec-data #:color 6 #:width 2 #:label "Rate")
       (points rel-states-per-sec-data #:color 5 #:line-width 2))
      #:y-min 1 #:x-label "Optimiziation")


discrete-histogram