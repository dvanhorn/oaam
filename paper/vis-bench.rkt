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

(define ((mk-de-inf default) n) (if (infinite? n) default n))
(define (numbers->relative bench-name accessors exponents [de-inf #f])
  (define bench-timing (hash-ref timings bench-name))
  (define baseline-numbers (hash-ref bench-timing "sp"))
  (define baseline-avgs
    (for/list ([acc accessors]) (vector-avg (acc baseline-numbers))))
  (define de-inf-default (mk-de-inf 1))
  (flatten
  (for/list ([acc accessors]
             [base baseline-avgs]
             [k exponents]
             [unbad (or de-inf (constant-stream de-inf-default))]) ;; base/num or num/base? (expt n 1), (expt n -1)
    (define unbad* (or unbad de-inf-default))
    (for/list ([(key desc) (in-pairs algo-name)]
               [n (in-naturals)])
      (vector n 
              (expt
               (unbad*
               (/ base
                  (vector-avg (acc (hash-ref bench-timing key)))))
               k))))))


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
                (-9 . 200)))
(define ytranss (list log-transform #f #f))
(define ytickss (list log-ticks #f #f))
(define de-inf (list (mk-de-inf (* 30 60 1000)) (mk-de-inf (* 1024 1024 1024)) (mk-de-inf 0)))

(define (sec-labels sec->anchor data)
  (map (λ (v l) (point-label v l #:anchor (sec->anchor l) #:point-size 12))
       data
       sections))

(parameterize ([plot-x-ticks no-ticks]
               [plot-font-size 11]
               [plot-width (* (plot-width) 2)]
               [plot-height (inexact->exact (truncate (/ (plot-height) 1.8)))])
  (for/list ([acc accs]
             [exp exps]
             [desc descs]
             [(ymin ymax) (in-pairs ymins)]
             [(xmin xmax) (in-pairs xmins)]
             [ytrans ytranss]
             [yticks ytickss])
    (parameterize ([plot-y-transform (or ytrans (plot-y-transform))]
                   [plot-y-ticks (if yticks (yticks) (plot-y-ticks))])
      (plot (cons
             (x-ticks (for/list ([sec sections]
                                 [i (in-naturals)])
                        (tick i #t sec)))
             (for/list ([bench (list "church" "maze" "nucleic" "boyer" "matrix" "lattice" "earley" "mbrotZ" "nbody" "graphs")]
                        [col (in-naturals)])
               (define data (numbers->relative bench (list acc) (list exp)))
               (list
                (lines data #:color (if (> col 4)
                                        "black"
                                        "gray")
                       #:style col #:width 2
                       #:label bench)
                #;(sec-labels sec->anchor data))))
            #:y-min ymin
            #:y-max ymax
            #:x-label ""
            #:x-min xmin
            #:x-max xmax
            #:y-label "" #;"Factor improvement over baseline"
            #:out-file (format "all-relative-~a.ps" desc))
            )))