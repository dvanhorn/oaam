#lang racket
(require plot "proctime.rkt" pict)

(define (adjusted-length v)
  (for/sum ([i v] #:when (number? i)) 1))
(define (average-vec v) ;; 'unset means no average
  (define sum (for/sum ([i v] #:when (number? i)) i))
  (define len (adjusted-length v))
  (and (not (zero? len)) (/ sum len)))
(define (variance-vec v)
  (define avg (average-vec v))
  (define len (adjusted-length v))
  (and avg
       (/ (for/sum ([i v]) (sqr (- i avg))) len)))
(define (stddev-vec v)
  (define var (variance-vec v))
  (and var (sqrt var)))

(define algo-name
  '(#;("bl" . "baseline")
    ("ps" . "baseline") ;; Specialized is the new baseline
    ("psp" . "pushdown")
    ("pspm" . "summaries")
    #;("pt" . "preallocated timestamp")
    ))

(define (c x) (- (sub1 x))) ;; neg for B/W, pos for color
(define (next x) (sub1 x))

(define (get-numbers tag sel sel-default [baseline-tag #f])
  (define (scale x) (if (number? x) x 0))
  (for*/list ([(name numbers) (in-hash timings)]
              #:unless (or (string=? name "church") (string=? name "maze"))
              [n (in-value (hash-ref numbers tag))])
    (define base-n (and baseline-tag (hash-ref numbers baseline-tag)))
    (define num (or (average-vec (sel n)) sel-default))
    (define err (or (stddev-vec (sel n)) 0))
    (define-values (base-num base-err)
      (if base-n
          (values (or (average-vec (sel base-n)) sel-default)
                  (or (stddev-vec (sel base-n)) 0))
          (values 1 0)))
    (define r (/ num base-num))
    (define frac-error (* r (+ (/ err num) (/ base-err base-num))))
    (list name r frac-error)))

(define (bench-plot sel sel-default y-label x-label out-file [baseline #f] [ignore '()])
  (plot 
   (let-values ([(hists errors)
                 (for/fold ([plots '()] [errors '()])
                     ([(tag algo) (in-dict algo-name)]
                      [i (in-naturals)]
                      #:unless (and baseline (member tag (cons baseline ignore))))
                   (define numbers* (get-numbers tag sel sel-default baseline))
                   (define skip 5.5)
                   (define error
                     ;; For current algo, give error bars for each benchmark.
                     (error-bars (for/list ([x numbers*] [m (in-naturals)])
                                   (list (+ 1/2 i (* m skip))
                                         (second x)
                                         (third x)))
                                 #:x-min i
                                 #:add-ticks? #f))
                   (values
                    (cons (discrete-histogram (for/list ([x numbers*]) (list (first x) (second x)))
                                              #:label algo
                                              #:skip skip #:x-min i
                                              #:style (add1 (* 2 i))
                                              #:color -7
                                              #:line-color "black")
                          plots)
                    (cons error errors)))])
     (append (reverse hists) (reverse errors)))
   #:y-label y-label
   #:x-label x-label
   #:legend-anchor 'top-left
   #:out-file out-file))

(define (do-with-params thunk)
  (parameterize (#;[plot-y-transform (axis-transform-bound log-transform 90000 1)]
               #;[plot-y-ticks     (log-ticks)]
                 [plot-jpeg-quality 30]
                 [plot-x-ticks no-ticks]
               [plot-font-size 20]
               [plot-x-tick-label-anchor 'top-right]
               [plot-x-tick-label-angle 60]
               [line-color  "black"]
               [interval-color  "black"]
               [interval-line1-color  "black"]
               [interval-line2-color  "black"]
               [plot-width (* 2 (plot-width))])
  (thunk)))

(define (states-per-second)
  (bench-plot numbers-state-rate 0 ;; errors since this should still exist in timeout
              "States-per-second (bigger is better)"
              "Benchmark"
              "state-per-sec.pdf"
              "ps"
              '("psp")))

(define (abs-time)
  (bench-plot numbers-run 3600000 ;; milliseconds to timeout 1000 * 3600
              "Analysis time (smaller is better)"
              "Benchmark"
              "abs-time.pdf"
              "ps"
              '("psp")))

(define (peak-mem)
  (bench-plot numbers-peak-mem (* 2 (expt 2 30)) ;; 2 GiB
              "Peak memory (smaller is better)"
              "Benchmark"
              "peak-mem.pdf"
              "ps"
              '("psp")))

(do-with-params states-per-second)
(do-with-params abs-time)
(do-with-params peak-mem)
