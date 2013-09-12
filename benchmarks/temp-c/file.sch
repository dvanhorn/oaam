(define (opener file)
  (define ports (open-input-output-file file))
  (define ip (car ports))
  (define op (cdr ports))
  (define reader (λ () (read-string 4096 ip)))
  (define writer (λ (s) (write s op)))
  (define closer (λ ()
                    (close-input-port ip)
                    (close-output-port op)))
  (cons reader (cons writer closer)))
(define copener
  (tmon 'user 'context 'contract
        ('open : string? -> (cons/c
                             (-> string?)
                             (cons/c
                              (string? -> void?)
                              (-> void?))))
        (· (* (!ret (label open) _))
           (bind (ret (label open) (cons (? reader) (cons (? writer) (? closer)) ))
            (·
             (* (!ret ($ closer) _))
             (ret ($ closer) _)
             (* (∩ (!call ($ reader))
                   (!call ($ writer) _)
                   (!call ($ closer)))))))
        opener))

(define from-files 
  (list "A.txt"
        "B.txt"
        "C.txt"
        "D.txt"))
(define to-files
  (list "0.txt"
        "1.txt"
        "2.txt"
        "3.txt"))
(define (for-each2 f lst1 lst2)
  (cond
   [(null? lst1) (void)]
   [(null? lst2) (void)]
   [else
    (f (car lst1) (car lst2))
    (for-each2 f (cdr lst1) (cdr lst2))]))

(for-each2 (λ (from to)
        (define f-fns (copener from))
        (define t-fns (copener to))
        (define f-read (car f-fns))
        (define f-close (cdr (cdr f-fns)))
        (define t-write (car (cdr t-fns)))
        (define t-close (cdr (cdr t-fns)))
        (t-write (f-read))
        (f-close)
        (t-close))
     from-files to-files)