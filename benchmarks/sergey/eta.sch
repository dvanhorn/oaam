;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/eta.scm
(define (do-something _) ;; FIXME should be nullary
  10)

(define (id y)
  (do-something #f) ;; FIXME nullary
  y)

((id (lambda (a) a)) #t)
((id (lambda (b) b)) #f)