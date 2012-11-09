#lang racket
(require plot "proctime.rkt" "procmem.rkt")

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
  '(("bl" . "baseline")
    ("sp" . "specialized")
    ("ls" . "lazy")
    ("lc" . "compiled")
    ;("ld" . "deltas")
    ("li" . "imperative")
    ("lp" . "preallocated")))

(define (c x) (+ x)) ;; neg for B/W, pos for color

(plot-width (* 2 (plot-width)))
(plot-height (* 2 (plot-height)))

(define (p)
  (let ([which run])
    (plot (for/list ([(name numbers) (in-hash timings)]
                     [i (in-naturals)])
            (define (scale x) (if (number? x) x (* 30 60 1000)))
            (define baseline (scale (average (which (hash-ref numbers "bl")))))
            (define numbers* (for*/list ([(tag algo) (in-dict algo-name)]
                                         #:unless (string=? tag "bl")
                                         [n (in-value (hash-ref numbers tag))])
                               (vector algo (/ (scale (average (which n))) baseline))))
            (discrete-histogram numbers*
                                #:label name
                                #:skip 10.5 #:x-min i
                                #:color (c (add1 i)) #:line-color (c (add1 i))))
          
          #:y-label "Time relative to baseline (smaller is better)"
          #:x-label "Optimization technique (cumulative, left to right)"
          #:legend-anchor 'top-right)))

(p)
(parameterize ([plot-y-transform (axis-transform-bound log-transform 0.0001 1)]
               #;[plot-y-ticks     (log-ticks)])
  (p))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The following are other examples of presentation from David
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#;
(plot (discrete-histogram (list #(a .5) #(b .4) #(c .3) #(d .2)
                                 #(e .1) #(f .05) #(g .01))
                           #:label "Nucleic")
       #:y-label "Time relative to baseline (smaller is better)"
       #:x-label "Optimization technique")

#|
Instead of n-graphs, one per benchmark, I could generate a single big
histogram like this:
|#
#;
(plot (list (discrete-histogram (list #(a .5) #(b .4) #(c .3) #(d .2)
                                       #(e .1) #(f .05) #(g .01))
                                 #:label "Nucleic"
                                 #:skip 2.5 #:x-min 0
                                 #:color 1 #:line-color 1)
             (discrete-histogram (list #(a .45) #(b .42) #(c .31) #(d .17)
                                       #(e .1) #(f .03) #(g .02))
                                 #:label "Mandelbrot"
                                 #:skip 2.5 #:x-min 1
                                 #:color 2 #:line-color 2))

       #:y-label "Time relative to baseline (smaller is better)"
       #:x-label "Optimization technique"
       #:legend-anchor 'top-right)
