;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/eta.scm
(define (do-something)
  10)

(define (id y)
  (do-something)
  y)

((id (lambda (a) a)) #t)
((id (lambda (b) b)) #f)
