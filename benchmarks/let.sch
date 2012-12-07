(define (f x y)
  (let ([y x]
        [x y])
    (cons x y)))
(f 0 1)