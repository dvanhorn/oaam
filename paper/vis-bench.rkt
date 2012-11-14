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

(define (constant-stream c)
  (make-do-sequence (λ ()
                      (values (λ _ c) (λ _ #f) #f (λ _ #t) (λ _ #t) (λ _ #t)))))

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

(define (numbers->relative bench-name accessors exponents defaults)
  (define bench-timing (hash-ref timings bench-name))
  (define baseline-numbers (hash-ref bench-timing "sp"))
  (define baseline-avgs
    (for/list ([acc accessors]) (vector-avg (acc baseline-numbers))))
  (flatten
  (for/list ([acc accessors]
             [base baseline-avgs]
             [k exponents]
             [d defaults]) ;; base/num or num/base? (expt n 1), (expt n -1)
    (for/list ([(key desc) (in-pairs algo-name)]
               [n (in-naturals)])
      (define avg (vector-avg (acc (hash-ref bench-timing key))))
      (vector n
              (cond [(and (infinite? base) (infinite? avg))
                      1]
                     [(infinite? base) (expt (/ d avg) k)]
                     [(infinite? avg) (expt (/ base d) k)]
                     [else (expt (/ base avg) k)]))))))


(define (sec->anchor l)
  (case l
    (("§4") 'bottom-left)
    (("§5.4" "§5.5") 'top)
    (else 'bottom)))

(define (sec-mem->anchor l)
  (case l
    (("§4") 'bottom-left)
    (else 'top)))    

(define sections
  (list "§4"
        "§5.1"
        "§5.2"
        "§5.3"
        "§5.4"
        "§5.5"))

(define accs (list numbers-run numbers-peak-mem numbers-state-rate))
(define exps (list 1 ;; Base / New number grows since time goes down
                   1 ;; Base / new same
                   -1)) ;; Rate goes up
(define descs (list "time" "memory" "speed"))
(define xmins '((0 . 5.2)
                (0 . 5.2)
                (0 . 5.2)))
(define ymins '((0.9 . 4300)
                (0 . 8)
                (0.1 . 2000)))
(define ytranss (list log-transform #f log-transform))
(define ytickss (list log-ticks #f log-ticks))
(define defaults (list (* 30 60 1000) (* 1024 1024 1024) 1))

(define (sec-labels sec->anchor data)
  (map (λ (v l) (point-label v l #:anchor (sec->anchor l) #:point-size 12))
       data
       sections))

(define ((unbend data) x)
  (define-values (firstx firsty nextx nexty)
    (let* ([firstx
            (for/last ([v data]
                       [i (in-naturals)]
                       #:when (>= x (vector-ref v 0)))
              i)]
           [firstx (or firstx 0)]
           [nextx (if (and firstx (< firstx (sub1 (length data))))
                      (add1 firstx)
                      (sub1 (length data)))])
      (values firstx (vector-ref (list-ref data firstx) 1)
              nextx (vector-ref (list-ref data nextx) 1))))
  (define dx (- nextx firstx))
  (cond [(zero? dx) firsty]
        [(zero? nexty) nexty]
        [else
         (define c (/ (log (/ nexty firsty)) dx))
         (* firsty (exp (* c (- x firstx))))]))

(parameterize ([plot-x-ticks no-ticks]
               [plot-font-size 13]
               [plot-width (* (plot-width) 2)]
               [plot-height (inexact->exact (truncate (/ (plot-height) 1.4)))])
  (for/list ([acc accs]
             [exp exps]
             [desc descs]
             [(ymin ymax) (in-pairs ymins)]
             [(xmin xmax) (in-pairs xmins)]
             [ytrans ytranss]
             [yticks ytickss]
             [default defaults])
    (parameterize ([plot-y-transform (or ytrans (plot-y-transform))]
                   [plot-y-ticks (if yticks (yticks) (plot-y-ticks))])
      (plot (cons
             (x-ticks (for/list ([sec sections]
                                 [i (in-naturals)])
                        (tick i #t sec)))
             (for/list ([bench (list "church" "maze" "nucleic" "boyer" "matrix" "lattice" "earley" "mbrotZ" "nbody" "graphs")]
                        [i (in-naturals)])
               (define col (if (> i 4) "black" "gray"))
               (define data (numbers->relative bench (list acc) (list exp) (list default)))
               (list
                (if ytrans
                    (function (unbend data) #:color col #:style i #:width 2 #:label bench)
                    (lines data #:color col #:style i #:width 2 #:label bench))
                #;(sec-labels sec->anchor data))))
            #:y-min ymin
            #:y-max ymax
            #:x-label ""
            #:x-min xmin
            #:x-max xmax
            #:y-label "" #;"Factor improvement over baseline"
            #:out-file (format "all-relative-~a.ps" desc))
            )))