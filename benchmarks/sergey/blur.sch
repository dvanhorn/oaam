(define id (lambda (x) x))
(define blur (lambda (y) y))
(define lp
  (lambda (a)
    (lambda (n)
      (if (zero? n)
	  (id a)
	  (let* ((r ((blur id) #t))
		 (s ((blur id) #f)))
	    (not (((blur lp) s) (sub1 n))))))))

((lp #f) 2)
