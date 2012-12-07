(let* ((count (read))
       (output (read)))
  (let ([ok?
         (lambda (result) (= result output))]
        [thunk (lambda () (printf "Thunk") (sub1 1))])
    (let loop ([i 0]
               [result (void)])
      (cond [(< i count) (loop (+ i 1) (thunk))]
            [(ok? result) result]
            [else
             (display "ERROR: returned incorrect result: ")
             (write result)
             (newline)
             result]))))