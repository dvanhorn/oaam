#lang racket
(require plot "proctime.rkt" "../code/notation.rkt")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generate numbers tabular (Program, LOC, Time (ms), Space (mb), Speed (states/sec)
(require (submod "../code/drive-benchmarks.rkt" data))

(define (file->name s)
  (define path (string->path s))
  (define-values (base filename dir?) (split-path path))
  (path->string (path-replace-suffix filename "")))
(define (loc f)
  (with-input-from-file f
    (λ ()
       (for/sum ([l (in-port read-line)]) #:break (eq? l 'eof) 1))))
(define (entry name fn n)
  (match (average (fn n))
    [#f (cond [(vector-ref (numbers-timeout? n) 0)
               "t"]
              [(vector-ref (numbers-exhaust? n) 0)
               "m"]
              [else (error 'bench-overview "No numbers, timeout or oom!: ~a" name)])]
    [n (number->string (inexact->exact (truncate n)))]))

(define files (list nucleic matrix nbody earley maze church lattice boyer mbrotZ))
(define comparisons (list numbers-run numbers-peak-mem numbers-state-rate))
(define algos (list "sp" "pd"))

(with-output-to-file "bench-overview.tex" #:mode 'text #:exists 'replace
  (λ ()
     (printf "\\begin{tabular}{@{}l|r|r|r|r|r|r|r@{}}~%")
     (printf "Program & LOC~%")
     (printf "& \\multicolumn{2}{c|}{Time (ms)}~%")
     (printf "& \\multicolumn{2}{c|}{Space (mb)}~%")
     (printf "& \\multicolumn{2}{c@{}}{Speed (state/sec)}~%")
     (printf "\\\\~%")
     (printf "\\hline\\hline~%")
     (printf
      (string-join
       (for/list ([file files])
         (define name (file->name file))
         (define numbers (hash-ref timings name))
         (format "~a & ~a & ~a"
                 name
                 (loc file)
                 (string-join
                  (for/append ([fn comparisons])
                    (for/list ([algo algos])
                      (entry `(,name ,algo) fn (hash-ref numbers algo))))
                  " & ")))
       " \\\\~%"))
     (printf "~%\\end{\\tabular}~%")))