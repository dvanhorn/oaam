#lang racket
(require plot)

(define algo-name
  '(("bl" . "baseline")
    ("sp" . "specialized")
    ("ls" . "lazy")
    ("lc" . "compiled")
    ("ld" . "deltas")
    ("li" . "imperative")
    ("lp" . "preallocated")))

;; Numbers are run time in ms
;; TODO: Change numbers to List[Number] and present the average ± variance
(define benchmarks
  (hash "church"
        (hash
         "bl" 72055
         "sp" 48153
         "lc" 7122
         "ls" 30463 ;;<-incorrect 74959
         "ld" 1639 ;; correct
         "li" 171
         "lp" 164)
        "mbrotZ"
        (hash
         "bl" 486360
         "sp" 410266
         "ls" 333572
         "lc" 59849
         "ld" 3413
         "li" 118
         "lp" 112)
        "earley"
        (hash
         "bl" 1313930
         "sp" 1227394
         "ls" 1065241
         "lc" 196274
         "ld" 7754
         "li" 746
         "lp" 669)
        "lattice"
        (hash
         "bl" 482237
         "sp" 381727
         "ls" 343567
         "lc" 79965
         "ld" 3779
         "li" 449
         "lp" 417)
        "nbody"
        (hash
         "bl" 'timeout
         "sp" 'timeout
         "ls" 'timeout
         "lc" 413912
         "ld" 995819
         "li" 44536
         "lp" 37720)
        "boyer"
        (hash
         "bl" 'timeout
         "sp" 'timeout
         "ls" 'timeout
         "lc" 'timeout
         "ld" 1063088
         "li" 15584
         "lp" 11267)
        "graphs"
        (hash
         "bl" 'timeout
         "sp" 'timeout
         "ls" 'timeout
         "lc" 'timeout
         "ld" 82241
         "li" 6681
         "lp" 5777)
        "matrix"
        (hash
         "bl" 'timeout
         "sp" 'timeout
         "ls" 'timeout
         "lc" 'timeout
         "ld" 66668
         "li" 7071
         "lp" 5656)
        "nucleic"
        (hash
         "bl" 'oom
         "sp" 'oom
         "ls" 'oom
         "lc" 'oom
         "ld" 'timeout
         "li" 153767
         "lp" 146727)
        "maze"
        (hash
         "bl" 'unknown
         "sp" 'unknown
         "ls" 'unknown
         "lc" 'unknown
         "ld" 81845
         "li" 'unknown
         "lp" 'unknown)))

(define (c x) (+ x)) ;; neg for B/W, pos for color

(plot-width (* 2 (plot-width)))
(plot-height (* 2 (plot-height)))

(plot (for/list ([(name numbers) (in-hash benchmarks)]
                 [i (in-naturals)])
        (define (scale x) (if (number? x) x 3600000))
        (define baseline (scale (hash-ref numbers "bl")))
        (define numbers* (for*/list ([(tag algo) (in-dict algo-name)]
                                     #:unless (string=? tag "bl")
                                     [n (in-value (hash-ref numbers tag))])
                           (vector algo (/ (scale n) baseline))))
        (discrete-histogram numbers*
                            #:label name
                            #:skip 7.5 #:x-min i
                            #:color (c (add1 i)) #:line-color (c (add1 i))))

      #:y-label "Time relative to baseline (smaller is better)"
      #:x-label "Optimization technique (cumulative, left to right)"
      #:legend-anchor 'top-right)

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
