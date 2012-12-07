(define (ηcons a b) (cons a b))
(define (ηcons2 a b) (cons a b))
(define (other . x) x)
(apply other 6 7 '(8))
#;
(cons
 (apply ηcons '(0 1))
 (cons
  (apply ηcons2 2 '(3))
  (cons
   (apply ηcons 4 5 '())
   (apply other 6 7 '(8)))))