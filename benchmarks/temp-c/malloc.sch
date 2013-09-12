(define addr? number?)
(define (with-malloc f)
  (define i 0)
  #;
  (define MallocFreeImpl
    )
  (define contracted
    (tmon 'user 'context 'contract
          (cons/c ('malloc : -> addr?)
                  ('free : addr? -> void?))
          (¬ (· (* (!call (label free) _))
                (bind (call (label free) (? addr))
                      (· (* (!ret (label malloc) ($ addr)))
                         (call (label free) ($ addr)))))) 
          (cons (λ () (let ([res i]) (set! i (add1 i)) res))
                (λ (a) (void)))))
  (f (car contracted) (cdr contracted)))

(define (good malloc free)
  (define a (malloc))
  (free a)
  (define e (malloc))
  (define f (malloc))
  (free e)
  (free f)
  (define c (malloc))
  (define d (malloc))
  (free d)
  (free c))

(define (bad malloc free)
  (define b (malloc))
  (free b)
  (free b))
;; can't verify due to weak accounting for numbers
;(with-malloc good)
(with-malloc bad)
