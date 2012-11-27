(define (id x) x)

(define (f n)
  (cond [(<= n 1) 1]
        [else (* n (f (sub1 n)))]))

(define (g n)
  (cond [(<= n 1) 1]
        [else (+ (* n n) (g (sub1 n)))]))

(+ ((id f) 3) ((id g) 4))