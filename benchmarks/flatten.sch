(define (flatten x)
  (cond
   ((pair? x)
    (append (flatten (car x)) (flatten (cdr x))))
   ((null? x) x)
   (else (list x))))

(flatten '((1 2) (((3 4 5)))))