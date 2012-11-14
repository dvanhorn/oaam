#lang racket
(require "proctime.rkt"
         unstable/sequence
         plot)

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


;; You can change this to get charts for other benchmarks but
;; likely that you have to tweak the max/min parameters below.
(define bench-name "church")

(define bench-timing (hash-ref timings bench-name))
(define baseline-time
  (vector-avg (numbers-run (hash-ref (hash-ref timings bench-name) "sp"))))
(define baseline-mem
  (vector-avg (numbers-peak-mem (hash-ref (hash-ref timings bench-name) "sp"))))
(define baseline-rate
  (vector-avg (numbers-state-rate (hash-ref (hash-ref timings bench-name) "sp"))))
(define rel-time-data
  (for/list ([(key desc) (in-pairs algo-name)]
             [n (in-naturals)])
    (vector n 
            (/ baseline-time 
               (vector-avg (numbers-run (hash-ref bench-timing key)))))))
(define rel-mem-data
  (for/list ([(key desc) (in-pairs algo-name)]
             [n (in-naturals)])
    (vector n 
            (/ baseline-mem 
               (vector-avg (numbers-peak-mem (hash-ref bench-timing key)))))))
(define rel-states-per-sec-data
  (for/list ([(key desc) (in-pairs algo-name)]
             [n (in-naturals)])
    (vector n 
            (/ (vector-avg (numbers-state-rate (hash-ref bench-timing key)))
               baseline-rate))))
 
(parameterize ([plot-x-ticks  no-ticks]
               [plot-font-size 30]
               [plot-width (* (plot-width) 2)]
               [plot-height (quotient (plot-height) 2)])
  (list 
   (plot (list
          (lines rel-time-data #:color 2 #:width 4 
                 #:label "Total analysis time")
          (points rel-time-data #:color 1 #:line-width 2))
         #:y-min -25 
         #:y-max 270
         #:x-label ""
         #:x-min 0
         #:x-max 5.2
         #:y-label "" #;"Factor improvement over baseline"
         #:out-file (format "~a-relative-time.ps" bench-name))
   
   (plot (list
          (lines rel-states-per-sec-data #:color 6 #:width 4
                 #:label "Rate of state transitions")
          (points rel-states-per-sec-data #:color 5 #:line-width 2))
         #:y-min -9
         #:y-max 65
         #:x-min 0
         #:x-label ""
         #:x-max 5.2
         #:y-label ""
         #:out-file (format "~a-relative-speed.ps" bench-name))
   
   (plot (list
          (lines rel-mem-data #:color 4 #:width 4
                 #:label "Peak memory")
          (points rel-mem-data #:color 3 #:line-width 2))
         #:y-min 1
         #:y-max 1.49 
         #:x-label ""
         #:x-min 0
         #:x-max 5.2
         #:y-label ""
         #:out-file (format "~a-relative-space.ps" bench-name))))

  
  
  
  