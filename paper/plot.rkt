#lang racket
(require plot "proctime.rkt")

(define (adjusted-length v)
  (for/sum ([i v] #:when (number? i)) 1))
(define (average v) ;; 'unset means no average
  (define sum (for/sum ([i v] #:when (number? i)) i))
  (define len (adjusted-length v))
  (and (not (zero? len)) (/ sum len)))
(define (variance v)
  (define avg (average v))
  (define len (adjusted-length v))
  (and avg
       (/ (for/sum ([i v]) (sqr (- i avg))) len)))
(define (stddev v)
  (define var (variance v))
  (and var (sqrt var)))

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

(define (c x) (- (sub1 x))) ;; neg for B/W, pos for color
(define (next x) (sub1 x))



(define (states-per-second)
  (let ([which numbers-state-rate])
    (plot (for/list ([(name numbers) (in-hash timings)]
                     [i (in-naturals)])
            (define (scale x) (if (number? x) x 0))
            (define numbers* (for*/list ([(tag algo) (in-dict algo-name)]
                                         [n (in-value (hash-ref numbers tag))])
                               (vector algo (scale (average (which n))))))
            (discrete-histogram numbers*
                                #:label name
                                #:skip 10.5 #:x-min i
                                #:style i
                                #:color -7 #;(c (next i)) #:line-color "black" 
                                #:line-style i))
          
          #:y-label "States-per-second (bigger is better)"
          #:x-label "Optimization technique (cumulative, left to right)"
          #:legend-anchor 'top-left
          #:out-file "state-per-sec.ps")))


(parameterize (#;[plot-y-transform (axis-transform-bound log-transform 90000 1)]
               #;[plot-y-ticks     (log-ticks)]
               [plot-font-size 20]
               [line-color  "black"]
               [interval-color  "black"]
               [interval-line1-color  "black"]
               [interval-line2-color  "black"]
               [plot-width (* 2 (plot-width))])
  (states-per-second))


(define (abs-time)
  (let ([which numbers-run])
    (plot (for/list ([(name numbers) (in-hash timings)]
                     [i (in-naturals)])
            (define (scale x) (if (number? x) x (* 1.2 (expt 10 6))))
            (define numbers* (for*/list ([(tag algo) (in-dict algo-name)]
                                         [n (in-value (hash-ref numbers tag))])
                               (vector algo (scale (average (which n))))))
            (discrete-histogram numbers*
                                #:label name
                                #:skip 10.5 #:x-min i
                                #:style i
                                #:color -7 #;(c (next i)) #:line-color "black" 
                                #:line-style i))
          
          #:y-label "Analysis time (smaller is better)"
          #:x-label "Optimization technique (cumulative, left to right)"
          #:legend-anchor 'top-right
          #:out-file "abs-time.ps")))

(parameterize (#;[plot-y-transform (axis-transform-bound log-transform .0001 1)]
               #;[plot-y-ticks     (log-ticks)]
               [plot-font-size 20]
               [line-color  "black"]
               [interval-color  "black"]
               [interval-line1-color  "black"]
               [interval-line2-color  "black"]
               [plot-width (* 2 (plot-width))])
  (abs-time))

(define church-time (for/first ([(name numbers) (in-hash timings)]
                                #:when (string=? name "church"))
                      numbers))
                      
#;
(define (q)
  (let ([which run])
    (plot (let ()
            (define (scale x) (if (number? x) x (* 30 60 1000)))
            (define baseline (scale (average (which (hash-ref church-time "bl")))))
            (define numbers* (for*/list ([(tag algo) (in-dict algo-name)]
                                         ;;#:unless (string=? tag "bl")
                                         [n (in-value (hash-ref church-time tag))])
                               (vector algo (/ (scale (average (which n))) baseline))))
            (discrete-histogram numbers*
                                #:label "church"
                                #:skip 1.5 ;#:x-min 0
                                #:style 1
                                #:color -7 #;(c (next i)) #:line-color "black" 
                                #:line-style 1))
          
          #:y-label "Time relative to baseline on log scale (smaller is better)"
          #:x-label "Optimization technique (cumulative, left to right)"
          #:legend-anchor 'top-right
          #:out-file "rel-time-church.ps")))

#;
(parameterize ([plot-y-transform (axis-transform-bound log-transform 0.0001 1)]
               #;[plot-y-ticks     (log-ticks)]
               [plot-font-size 20]
               [line-color  "black"]
               [interval-color  "black"]
               [interval-line1-color  "black"]
               [interval-line2-color  "black"]
               #;[plot-height (* (plot-height))])
  (q))

(define (peak-mem)
  (let ([which numbers-peak-mem])
    (plot (for/list ([(name numbers) (in-hash timings)]
                     [i (in-naturals)])
            (define (scale x) (if (number? x) x (* 2.5 (expt 10 9))))
            (define numbers* (for*/list ([(tag algo) (in-dict algo-name)]
                                         [n (in-value (hash-ref numbers tag))])
                               (vector algo (scale (average (which n))))))
            (discrete-histogram numbers*
                                #:label name
                                #:skip 10.5 #:x-min i
                                #:style i
                                #:color -7 #;(c (next i)) #:line-color "black" 
                                 #:line-style i))
          
          #:y-label "Peak memory (smaller is better)"
          #:x-label "Optimization technique (cumulative, left to right)"
          #:legend-anchor 'top-right
          #:out-file "peak-mem.ps")))

(parameterize (#;[plot-y-transform (axis-transform-bound log-transform .0001 1)]
               #;[plot-y-ticks     (log-ticks)]
               [plot-font-size 20]
               [line-color  "black"]
               [interval-color  "black"]
               [interval-line1-color  "black"]
               [interval-line2-color  "black"]
               [plot-width (* 2 (plot-width))])
  (peak-mem))

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
