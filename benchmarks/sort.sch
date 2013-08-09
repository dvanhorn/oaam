(define narf #f)
(define (insert cmp)
  (λ (a lst)
     (set! narf cmp)
   (cond [(null? lst) (list a)]
         [else
          (define l0 (car lst))
          (if (cmp a l0)
              (cons a lst)
              (cons l0 ((insert cmp) a (cdr lst))))])))
(define (foldl f b lst)
  (if (null? lst)
      b
      (foldl f (f (car lst) b) (cdr lst))))
(define (sort cmp lst)
  (foldl (insert cmp) '() lst))
(define (listof f)
  (λ (lst)
   (or (null? lst)
       (and (f (car lst)) ((listof f) (cdr lst))))))
(define csort
 (tmon 'user 'context 'contract
       ('sort : ('cmp : integer? integer? -> boolean?)
               (listof integer?)
               ->
               (listof integer?))
       (and (not (seq ... (call 'sort _) (star (!ret 'sort _)) (call 'sort _)))
            (not (seq ... (bind (call 'sort (? cmp) _)
                                (seq ... (ret 'sort _)
                                     ... (call (? cmp) _ _))))))
       sort))

(csort (λ (x y) (<= x y)) (list 1 2 3 4))
#;(narf 0 1)