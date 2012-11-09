#lang racket/base
(require racket/sandbox)
(provide with-limit-handler state-rate)

(define (state-rate start-time-in-ms state-count)
  (define time-taken-in-seconds (/ (- (current-milliseconds) start-time-in-ms)
                                   1000))
  (printf "States/second: ~a~%" (exact->inexact ;; for decimal places
                                 (/ (if (box? state-count)
                                       (unbox state-count)
                                       state-count)
                                   time-taken-in-seconds))))

(define-syntax-rule (with-limit-handler (start-time state-count) body ...)
  (with-handlers ([exn:fail:resource?
                   (λ (e)
                      (state-rate start-time state-count)
                      (case (exn:fail:resource-resource e)
                        [(time) (dump-memory-stats) (printf "Result: Timeout~%")]
                        [(memory) (printf "Result: Exhausted memory~%")]))]
                  [exn:fail? (λ (e) (printf "Barf ~a" e))])
    body ...))