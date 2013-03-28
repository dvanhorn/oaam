#lang racket
(require "parse.rkt" "kcfa-instantiations.rkt" "LK-instantiations.rkt"
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

(define (test e)
  (parameterize ([current-logger (make-logger 'stuck-states)])
    #;#;
    (log-thread 'info)
    (log-thread 'debug)
    ;; we want to make sure that we are testing the implementation and not
    ;; Racket's startup cost.
    (collect-garbage)
    (collect-garbage)
    (collect-garbage)
    (with-limit-handler ;; Prints state rate even if timeout/oom
     (with-limits (* 30 #;run-for-30-minutes
                     60 #;seconds-in-minutes)
                  1024  ;; Max memory: 1GiB
                  (call-with-values (λ ()
                                       (begin0 (time ((aval) e))
                                               (void)
                                               (dump-memory-stats)
                                               (flush-output)
                                               (printf "Result: Complete~%")))
                    ;; Fixpoints return their results and strings with
                    ;; statistics in them. Print it all.
                    print-values)))))

(module+ main
  (require racket/cmdline)
  (define test-file
    (command-line #:once-any
                  [("--bl") "Benchmark baseline"
                   (aval baseline)] ;; least optimized
                  [("--sp") "Benchmark specialized fixpoint"
                   (aval 0cfa^)]
                  [("--spt") "Benchmark specialized fixpoint with timestamps"
                   (aval 0cfa^/t)]
                  [("--sdt") "Benchmark specialized fixpoint with timestamps and store deltas"
                   (aval 0cfa^-∆s/t)]
                  [("--ls") "Benchmark specialized lazy non-determinism"
                   (aval lazy-0cfa^)]
                  [("--lst") "Benchmark specialized lazy non-determinism with timestamps"
                   (aval lazy-0cfa^-∆s/t)]
                  [("--lc") "Benchmark compiled specialized lazy non-determinism"
                   (aval lazy-0cfa^/c)]
                  [("--lct") "Benchmark compiled specialized lazy non-determinism with timestamps"
                   (aval lazy-0cfa^-∆s/t/c)]
                  [("--ld")
                   "Benchmark compiled store-diff lazy non-determinism"
                   (aval lazy-0cfa^/c/∆s)]
                  [("--fd")
                   "Benchmark compiled store-diff lazy non-determinism functional timestamp nonapprox"
                   (aval lazy-0cfa^/c/∆s/t)]
                  [("--ia")
                   "Benchmark compiled imperative accumulated store-diff lazy non-determinism"
                   (aval lazy-0cfa^/c/∆s/acc!)]
                  [("--id")
                   "Benchmark compiled imperative store-diff lazy non-determinism"
                   (aval lazy-0cfa^/c/∆s!)]
                  [("--is")
                   "Benchmark compiled imperative stacked store lazy non-determinism"
                   (aval lazy-0cfa^/c/∆s/stacked!)]
                  [("--pa")
                   "Benchmark compiled preallocated accumulated store-diff lazy non-determinism"
                   (aval lazy-0cfa^/c/∆s/acc/prealloc!)]
                  [("--pd")
                   "Benchmark compiled preallocated store-diff lazy non-determinism"
                   (aval lazy-0cfa^/c/∆s/prealloc!)]
                  [("--ps")
                   "Benchmark compiled preallocated stacked store lazy non-determinism"
                   (aval lazy-0cfa^/c/∆s/prealloc/stacked!)]
                  [("--it")
                   "Benchmark compiled imperative store lazy non-determinism timestap approx"
                   (aval lazy-0cfa^/c/timestamp!)]
                  [("--pt")
                   "Benchmark compiled preallocated store lazy non-determinism timestamp approx"
                   (aval lazy-0cfa^/c/prealloc/timestamp!)] ;; most optimized
                  ;; Continuation-mark enabled analyses
                  [("--cb")
                   "Benchmark baseline continuation marks"
                   (aval baseline/cm)]
                  ;; Lazy language analysis
                  [("--kb")
                   "Benchmark baseline lazy-Krivine machine"
                   (aval LK-baseline)]
                  [("--kp")
                   "Benchmark best lazy-Krivine machine"
                   (aval LK-lazy-0cfa^/c/∆s/prealloc!)]
                  ;; Not benchmarked for paper
                  #|
                  [("--ls2") "Benchmark specialized2 lazy non-determinism"
                  (aval lazy-0cfa^2)]
                  [("--ls3") "Benchmark specialized3 lazy non-determinism"
                  (aval lazy-0cfa^3)]
                  [("--lazy-0cfa")
                  "Benchmark specialized narrow lazy non-determinism"
                  (aval lazy-0cfa)]
                  [("--lazy-0cfa/c")
                  "Benchmark specialized compiled narrow lazy non-determinism"
                  (aval lazy-0cfa/c)]
                  [("--lazy-0cfa-gen^/c")
                  "Benchmark compiled generators lazy non-determinism"
                  (aval lazy-0cfa-gen^/c)]
                  [("--lazy-0cfa^-gen-σ-∆s")
                  "Benchmark store-diff generators lazy non-determinism"
                  (aval lazy-0cfa-gen-σ-∆s^)]
                  [("--lazy-0cfa-gen-σ-∆s^/c")
                  "Benchmark compiled store-diff generators lazy non-determinism"
                  (aval lazy-0cfa-gen-σ-∆s^/c)]
                  [("--lazy-0cfa^/prealloc!")
                  "Benchmark preallocated store lazy non-determinism"
                  (aval lazy-0cfa^/prealloc!)]
                  |#
                #:args (filename)
                filename))
(test (prep test-file)))