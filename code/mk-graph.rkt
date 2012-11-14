#lang racket
(require "kcfa-instantiations.rkt" "run-benchmark.rkt" "graph.rkt" (only-in "data.rkt" cons-limit))

(define benchmark (make-parameter "/home/ianj/projects/xcfa/racket-impl/test-suite/introspective.sch"))
(define (prefix)
  (let-values ([(base filename dir?) (split-path (string->path (benchmark)))])
    filename))

(define (print-values . vs) (for ([v vs]) (display v) (newline)))

(define (do eval suffix)
  (thread
   (λ ()
      (define p (prefix))
      (define pdf (path-replace-suffix p (format "~a.pdf" suffix)))
      (parameterize ([graph-file (path-replace-suffix p (format "~a.dot" suffix))]
                     [aval eval])
        (call-with-values (λ () (test (prep (benchmark)))) values)
        #;
        (system (format "dot -Tpdf -o ~a ~a" pdf (graph-file)))))))

(define (all-three)
  (define ts (list (do 0cfa "-base")
                   (do lazy-0cfa "-lazy")
                   (do lazy-0cfa/c "-lazyc")))
  (for ([t ts]) (thread-wait t)))

(all-three)
