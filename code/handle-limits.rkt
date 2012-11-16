#lang racket/base
(require racket/sandbox)
(provide with-limit-handler state-count start-time state-rate)

(define state-count (make-parameter #f))
(define start-time (make-parameter #f))

(define (state-rate)
  (define time-taken-in-seconds (/ (- (current-milliseconds)
                                      (unbox (start-time)))
                                   1000))
  (printf "States/second: ~a~%" (exact->inexact ;; for decimal places
                                 (/ (unbox (state-count))
                                   time-taken-in-seconds))))

(define-syntax-rule (with-limit-handler body ...)
  (parameterize ([state-count (box #f)]
                 [start-time (box #f)])
    (with-handlers ([exn:fail:resource?
                     (λ (e)
                        (state-rate)
                        (case (exn:fail:resource-resource e)
                          [(time) (printf "Result: Timeout~%")]
                          [(memory) (printf "Result: Exhausted memory~%")]))]
                    [exn:fail? (λ (e) (printf "Barf ~a" e))])
      body ...
      (dump-memory-stats))))