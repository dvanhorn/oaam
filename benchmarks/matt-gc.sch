
(let lp1 ([i 10] [x 0])
  (if (zero? i)
      x
      (let lp2 ([j 10] [f (λ (n) (+ n i))] [y x])
        (if (zero? j)
            (lp1 (sub1 i) y)
            (lp2 (sub1 j) f (f y))))))
