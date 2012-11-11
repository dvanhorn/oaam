#lang racket
(require plot "proctime.rkt" #;"procmem.rkt")

(define (average v) ;; 'unset means no average
  (and (number? (vector-ref v 0))
       (/ (for/sum ([i v]) i) (vector-length v))))
(define (variance v)
  (define avg (average v))
  (and avg
       (/ (for/sum ([i v]) (sqr (- i avg))) (vector-length v))))
(define (stddev v)
  (define var (variance v))
  (and var (sqrt var)))

(define algo-name
  '(;;("bl" . "baseline")
    ("sp" . "baseline")
    ("ls" . "lazy")
    ("lc" . "compiled")
    ("ld" . "deltas")
    ("id" . "imperative")
    ("pd" . "preallocated")))

(define (c x) (- (sub1 x))) ;; neg for B/W, pos for color
(define (next x) (sub1 x))

(plot-width (* 2 (plot-width)))
(plot-height (* 3/2 (plot-height)))

(define (p)
  (let ([which numbers-run])
    (plot (for/list ([(name numbers) (in-hash timings)]
                     [i (in-naturals)])
            (define (scale x) (if (number? x) x (* 30 60 1000)))
            (define baseline (scale (average (which (hash-ref numbers "sp")))))
            (define numbers* (for*/list ([(tag algo) (in-dict algo-name)]
                                         #:unless (string=? tag "sp")
                                         [n (in-value (hash-ref numbers tag))])
                               (vector algo (/ (scale (average (which n))) baseline))))
            (discrete-histogram numbers*
                                #:label name
                                #:skip 10.5 #:x-min i
                                #:style i
                                #:color -7 #;(c (next i)) #:line-color "black"
                                #:line-style i))
          
          #:y-label "Time relative to baseline on log scale (smaller is better)"
          #:x-label "Optimization technique (cumulative, left to right)"
          #:legend-anchor 'top-right
          #:out-file "rel-time.ps")))

(parameterize ([plot-y-transform (axis-transform-bound log-transform 0.0001 1)]
               #;[plot-y-ticks (log-ticks)]
               [plot-font-size 20]
               [line-color "black"]
               [interval-color "black"]
               [interval-line1-color "black"]
               [interval-line2-color "black"])
  (p))