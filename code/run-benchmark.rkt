#lang racket
(require "parse.rkt" "kcfa-instantiations.rkt"
         ;; "LK-instantiations.rkt" FIXME
         "handle-limits.rkt"
         racket/sandbox)
(provide test aval prep)

(define (sch->sexp file)
  (with-input-from-file file
    (λ () (for/list ([form (in-port read)]) form))))

(define (prep file) (sch->sexp file))

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
    (with-limit-handler
      (with-limits (* 30 #;run-for-30-minutes
                      60 #;seconds-in-minutes)
                   1024 ;; Max memory: 1GiB
                   (call-with-values
                       (λ () (begin0 (time ((aval) e))
                                     (printf "Result: Complete~%")))
                     print-values)))))

(module+ main
 (require racket/cmdline)
 (define test-file
  (command-line #:once-any
                [("--n0cfa")
                 "Benchmark narrow compiled 0cfa"
                 (aval lazy-0CFA/c)]
                [("--g0cfa")
                 "Benchmark garbage-collected compiled 0cfa"
                 (aval lazy-ΓCFA/c)]
                [("--pt2")
                 "Benchmark compiled preallocated timestamp approx. cfa2"
                 (aval lazy-cfa2^/c/prealloc/timestamp!)]

                [("--sparsep")
                 "Benchmark compiled imperative sparse"
                 (aval sp-lazy-0cfa^/c)]
                [("--pts")
                 "Benchmark compiled preallocated timestamp approx. pdcfa"
                 (aval lazy-pdcfa^/c/prealloc/timestamp!)]
#|                [("--sid")
                 "Benchmark compiled imperative store-diff"
                 (aval 0cfa^/c/∆s!)]
                [("--spd")
                 "Benchmark compiled preallocated store-diff"
                 (aval 0cfa^/c/∆s/prealloc!)]
|#
#|
                [("--bl") "Benchmark baseline"
                 (aval baseline)] ;; least optimized
                [("--sp") "Benchmark specialized fixpoint"
                 (aval 0cfa^)]
                [("--ls") "Benchmark specialized lazy non-determinism"
                 (aval lazy-0cfa^)]
                [("--lc") "Benchmark compiled specialized lazy non-determinism"
                 (aval lazy-0cfa^/c)]
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
                [("--pa")
                 "Benchmark compiled preallocated accumulated store-diff lazy non-determinism"
                 (aval lazy-0cfa^/c/∆s/acc/prealloc!)]
|#
#;                [("--pd")
                 "Benchmark compiled preallocated store-diff lazy non-determinism"
                 (aval lazy-0cfa^/c/∆s/prealloc!)]
#|
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
|#
                ;; Not benchmarked for paper
#|
                [("--ls2") "Benchmark specialized2 lazy non-determinism"
                 (aval lazy-0cfa^2)]
                [("--ls3") "Benchmark specialized3 lazy non-determinism"
                 (aval lazy-0cfa^3)]
                [("--spp")
                 "Benchmark compiled preallocated store sparse lazy non-determinism"
                 (aval sparse-lazy-0cfa^/c/prealloc!)]
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
                #:multi
                [("-d") datum
                 "Print debug message if following datum interpreted"
                 (define d (with-input-from-string datum read))
                 (printf "Debug msg on ~v~%" d)
                 (debug-check (cons d (debug-check)))]
                #:args (filename)
                filename))
(test (prep test-file)))