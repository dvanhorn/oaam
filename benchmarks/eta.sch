;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/eta.scm
(let* ((do-something (lambda (_) 10))
       (id (lambda (y)
	     (let* ((__ (do-something 0)))
	       y))))
  (let* ((___ ((id (lambda (a) a)) #t)))
    ((id (lambda (b) b)) #f)))