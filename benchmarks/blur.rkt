#lang racket
;(require (only-in mzlib/etc rec))

(provide P)
(define P
  '(let* ((id (lambda (x) x))
	  (blur (lambda (y) y)))

     (((rec lp
         (lambda (a)
	   (lambda (n)
	     (if (zero? n)
		 (id a)
		 (let* ((r ((blur id) #t))
			(s ((blur id) #f)))
		   (not (((blur lp) s) (sub1 n))))))))
       #f)
      2)))
