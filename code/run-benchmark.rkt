#lang racket
(require "parse.rkt" #;"LK-instantiations.rkt"
         "handle-limits.rkt"
         racket/sandbox)
(provide test aval prep)

(define (sch->sexp file)
  (with-input-from-file file
    (λ () (for/list ([form (in-port read)]) form))))
;; Used to be different
(define prep sch->sexp)

(define-syntax-rule (log-thread kind)
  (let ([lr (make-log-receiver (current-logger) kind)])
    (thread (λ () (let loop () (define vs (sync lr)) (write vs) (newline) (loop))))))

(define (print-values . vs) (for ([v vs]) (display v) (newline)))

(define aval (make-parameter #f))
(define name (make-parameter #f))

(define (test e)
  (parameterize ([current-logger (make-logger 'stuck-states)])

    (log-thread 'info)
    (log-thread 'debug)
    ;; we want to make sure that we are testing the implementation and not
    ;; Racket's startup cost.
    (collect-garbage)
    (collect-garbage)
    (collect-garbage)
    (with-limit-handler ;; Prints state rate even if timeout/oom
     (call-with-limits (* 30 #;run-for-30-minutes
                     60 #;seconds-in-minutes)
                  2048  ;; Max memory: 1GiB
                  (λ ()
                     (aval (dynamic-require "kcfa-instantiations.rkt" (name)))
                     (call-with-values (λ ()
                                          (begin0 (time ((aval) e))
                                            (void)
                                            (dump-memory-stats)
                                            (flush-output)
                                            (printf "Result: Complete~%")))
                       ;; Fixpoints return their results and strings with
                       ;; statistics in them. Print it all.
                       print-values))))))

(module+ main
  (require racket/cmdline)
  (define test-file
    (command-line
     #:once-any
     [("--sp") "Specialized fixpoint"
      (name '0cfa^)]
     [("--spt") "Benchmark specialized fixpoint with timestamps"
      (name '0cfa^/t)]
     [("--sdt") "Benchmark specialized fixpoint with timestamps and store deltas"
      (name '0cfa^-∆s/t)]
     [("--ls") "Benchmark specialized lazy non-determinism"
      (name 'lazy-0cfa^)]
     [("--lc") "Benchmark compiled specialized lazy non-determinism"
      (name 'lazy-0cfa^/c)]
     [("--lst") "Benchmark specialized lazy non-determinism with timestamps"
      (name 'lazy-0cfa^-∆s/t)]
     [("--lct") "Benchmark compiled specialized lazy non-determinism with timestamps"
      (name 'lazy-0cfa^-∆s/t/c)]
     [("--ld")
      "Benchmark compiled store-diff lazy non-determinism"
      (name 'lazy-0cfa^/c/∆s)]
     [("--fd")
      "Benchmark compiled store-diff lazy non-determinism functional timestamp nonapprox"
      (name 'lazy-0cfa^/c/∆s/t)]
     [("--ia")
      "Benchmark compiled imperative accumulated store-diff lazy non-determinism"
      (name 'lazy-0cfa^/c/∆s/acc!)]
     [("--id")
      "Benchmark compiled imperative store-diff lazy non-determinism"
      (name 'lazy-0cfa^/c/∆s!)]
     [("--is")
      "Benchmark compiled imperative stacked store lazy non-determinism"
      (name 'lazy-0cfa^/c/∆s/stacked!)]
     [("--pa")
      "Benchmark compiled preallocated accumulated store-diff lazy non-determinism"
      (name 'lazy-0cfa^/c/∆s/acc/prealloc!)]
     [("--pd")
      "Benchmark compiled preallocated store-diff lazy non-determinism"
      (name 'lazy-0cfa^/c/∆s/prealloc!)]
     [("--ps")
      "Benchmark compiled preallocated stacked store lazy non-determinism"
      (name 'ps-aval)]
     [("--psp")
      "Benchmark compiled pushdown preallocated stacked store lazy non-determinism"
      (name 'psp-aval)]
     [("--psu")
      "Benchmark compiled preallocated stacked store lazy non-determinism with μ equality"
      (name 'psu-aval)]
     [("--lcg")
      "Benchmark compiled GCd abs-counted lazy non-determinism"
      (name 'lcg-aval)]
     [("--lcgt")
      "Benchmark compiled GCd abs-counted lazy non-determinism and weak references in Tcons"
      (name 'lcgt-aval)]
     [("--lcgut")
      "Benchmark compiled GCd abs-counted lazy non-determinism, weak references in Tcons and μ equality"
      (name 'lcgut-aval)]
     [("--lcgutp")
      "Benchmark compiled pushdown GCd abs-counted lazy non-determinism, weak references in Tcons and μ equality"
      (name 'lcgutp-aval)]
     [("--ps1")
      "Benchmark compiled preallocated stacked store lazy non-determinism k=1"
      (name 'lazy-1cfa^/c/∆s/prealloc/stacked!)]
     [("--it")
      "Benchmark compiled imperative store lazy non-determinism timestap approx"
      (name 'lazy-0cfa^/c/timestamp!)]
     [("--pt")
      "Benchmark compiled preallocated store lazy non-determinism timestamp approx"
      (name 'lazy-0cfa^/c/prealloc/timestamp!)] ;; most optimized
     ;; Continuation-mark enabled analyses
     [("--cb")
      "Benchmark baseline continuation marks"
      (name 'baseline/cm)]
     ;; Lazy language analysis
     [("--kb")
      "Benchmark baseline lazy-Krivine machine"
      (name 'LK-baseline)]
     [("--kp")
      "Benchmark best lazy-Krivine machine"
      (name 'LK-lazy-0cfa^/c/∆s/prealloc!)]
     ;; Not benchmarked for paper
     [("--ls2") "Benchmark specialized2 lazy non-determinism"
      (name 'lazy-0cfa^2)]
     [("--ls3") "Benchmark specialized3 lazy non-determinism"
      (name 'lazy-0cfa^3)]
     [("--lazy-0cfa")
      "Benchmark specialized narrow lazy non-determinism"
      (name 'lazy-0cfa)]
     [("--lazy-0cfa/c")
      "Benchmark specialized compiled narrow lazy non-determinism"
      (name 'lazy-0cfa/c)]
     [("--lazy-0cfa-gen^/c")
      "Benchmark compiled generators lazy non-determinism"
      (name 'lazy-0cfa-gen^/c)]
     [("--lazy-0cfa^-gen-σ-∆s")
      "Benchmark store-diff generators lazy non-determinism"
      (name 'lazy-0cfa-gen-σ-∆s^)]
     [("--lazy-0cfa-gen-σ-∆s^/c")
      "Benchmark compiled store-diff generators lazy non-determinism"
      (name 'lazy-0cfa-gen-σ-∆s^/c)]
     [("--lazy-0cfa^/prealloc!")
      "Benchmark preallocated store lazy non-determinism"
      (name 'lazy-0cfa^/prealloc!)]
     #:args (filename)
     filename))
(require "graph.rkt")
(parameterize ([graph-file "test.dot"])
 (test (prep test-file))))

;(define vis-bench (prep "/home/ianj/projects/xcfa/racket-impl/test-suite/introspective.sch"))
;
;;(parameterize ([graph-file "1.dot"] [aval 0cfa^]) (test vis-bench))
;;(parameterize ([graph-file "2.dot"] [aval lazy-0cfa^]) (test vis-bench))
;(parameterize ([graph-file "3.dot"] [aval lazy-0cfa^/c]) (test vis-bench))