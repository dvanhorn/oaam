#lang racket
(require "parse.rkt" "kcfa-instantiations.rkt"
         racket/sandbox
         racket/cmdline)

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
    (log-thread 'info)
    (log-thread 'debug)
    ;; we want to make sure that we are testing the implementation and not
    ;; Racket's startup cost.
    (collect-garbage)
    (collect-garbage)
    (collect-garbage)
    (with-handlers ([exn:fail:resource?
                     (λ (e) (case (exn:fail:resource-resource e)
                              [(time) (dump-memory-stats) (flush-output)
                               (printf "Result: Timeout~%")]
                              [(memory) (printf "Result: Exhausted memory~%")]))]
                    [exn:fail? (λ (e) (printf "Barf ~a ~%" e))])
      (with-limits 3600 2048
                   (begin0 (time ((aval) e))
                           (void)
                           (dump-memory-stats)
                           (flush-output)
                           (printf "Result: Complete~%"))))))

(define test-file
  (command-line #:once-any
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
                 (aval lazy-0cfa∆/c)]
                [("--li")
                 "Benchmark compiled imperative store lazy non-determinism"
                 (aval lazy-0cfa^/c!)]
                [("--lp")
                 "Benchmark compiled preallocated store lazy non-determinism"
                 (aval lazy-0cfa^/c/prealloc!)] ;; most optimized
                ;; Not benchmarked for paper
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
                 (aval lazy-0cfa^-gen-σ-∆s)]
                [("--lazy-0cfa-gen-σ-∆s^/c")
                 "Benchmark compiled store-diff generators lazy non-determinism"
                 (aval lazy-0cfa-gen-σ-∆s^/c)]
                [("--lazy-0cfa^/prealloc!")
                 "Benchmark preallocated store lazy non-determinism"
                 (aval lazy-0cfa^/prealloc!)]
                #:args (filename)
                filename))
(test (prep test-file))