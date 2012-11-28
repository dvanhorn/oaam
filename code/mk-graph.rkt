#lang racket
(require "kcfa-instantiations.rkt" "run-benchmark.rkt" "graph.rkt" (only-in "data.rkt" cons-limit))
(require racket/stxparam)

(define benchmark (make-parameter "../benchmarks/introspective.sch"))
(define (prefix)
  (let-values ([(base filename dir?) (split-path (string->path (benchmark)))])
    filename))

(define (print-values . vs) (for ([v vs]) (display v) (newline)))

(define (do eval suffix)
  (thread
   (λ ()
      (define p (prefix))
      (syntax-parameterize ([generate-graph? #t])
        (parameterize ([graph-file (path-replace-suffix p (format "~a.dot" suffix))]
                       [aval eval])
          (call-with-values (λ () (test (prep (benchmark)))) values))))))

(define (all-three)
  (define ts (list (do 0cfa^ "-base")
                   (do lazy-0cfa^ "-lazy")
                   (do lazy-0cfa^/c "-lazyc")))
  (for ([t ts]) (thread-wait t)))

(all-three)
