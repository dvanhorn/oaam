(define (call-me-first x) x)
(define (foo y) y)
(define (bar z) z)

(define all
  (tmon 'user 'context 'contract
        (cons/c ('fst : any -> any)
                (cons/c ('foo : any -> any)
                        ('bar : any -> any)))
        (not (· (* (!ret (label fst) _))
                ;; Don't call foo or bar if haven't returned from fst yet.
                (∪ (call (label foo) _)
                   (call (label bar) _))))
        (cons call-me-first (cons foo bar))))
(define cfirst (car all))
(define cfoo (car (cdr all)))
(define cbar (cdr (cdr all)))

(cbar (cfoo 1))