#lang racket

(require "parse.rkt" "ast.rkt" "notation.rkt")
(provide add-lib)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-primitive primitives.

;; Needed since we have a whole program analysis yet benchmarks that
;; expect common functions like "append"
;; Taken mostly verbatim from Jagannathan and Wright's polycfa implementation

(define r4rs-prims
  (make-hasheq
   `((/ . (lambda (n . ms)
            (if (null? ms)
                (binary-/ 1 n)
                (let loop ([acc n] [ms ms])
                  (if (pair? ms)
                      (loop (binary-/ acc (car ms)) (cdr ms))
                      acc)))))
     (+ . (lambda ns (let loop ([acc 0] [ns ns])
                       (if (pair? ns)
                           (loop (binary-+ acc (car ns)) (cdr ns))
                           acc))))
     (* . (lambda ns (let loop ([acc 1] [ns ns])
                       (if (pair? ns)
                           (loop (binary-* acc (car ns)) (cdr ns))
                           acc))))
     (vector . (lambda ns
                 (define v (make-vector (length ns)))
                 (let loop ([ns ns] [i 0])
                   (if (pair? ns)
                       (begin (vector-set! v i (car ns))
                              (loop (cdr ns) (add1 i)))
                       (void)))
                 v))
     (caar . (lambda (x) (car (car x))))
     (cadr . (lambda (x) (car (cdr x))))
     (cdar . (lambda (x) (cdr (car x))))
     (cddr . (lambda (x) (cdr (cdr x))))
     (caaar . (lambda (x) (car (car (car x)))))
     (caadr . (lambda (x) (car (car (cdr x)))))
     (cadar . (lambda (x) (car (cdr (car x)))))
     (caddr . (lambda (x) (car (cdr (cdr x)))))
     (cdaar . (lambda (x) (cdr (car (car x)))))
     (cdadr . (lambda (x) (cdr (car (cdr x)))))
     (cddar . (lambda (x) (cdr (cdr (car x)))))
     (cdddr . (lambda (x) (cdr (cdr (cdr x)))))
     (caaaar . (lambda (x) (car (car (car (car x))))))
     (caaadr . (lambda (x) (car (car (car (cdr x))))))
     (caadar . (lambda (x) (car (car (cdr (car x))))))
     (caaddr . (lambda (x) (car (car (cdr (cdr x))))))
     (cadaar . (lambda (x) (car (cdr (car (car x))))))
     (cadadr . (lambda (x) (car (cdr (car (cdr x))))))
     (caddar . (lambda (x) (car (cdr (cdr (car x))))))
     (cadddr . (lambda (x) (car (cdr (cdr (cdr x))))))
     (cdaaar . (lambda (x) (cdr (car (car (car x))))))
     (cdaadr . (lambda (x) (cdr (car (car (cdr x))))))
     (cdadar . (lambda (x) (cdr (car (cdr (car x))))))
     (cdaddr . (lambda (x) (cdr (car (cdr (cdr x))))))
     (cddaar . (lambda (x) (cdr (cdr (car (car x))))))
     (cddadr . (lambda (x) (cdr (cdr (car (cdr x))))))
     (cdddar . (lambda (x) (cdr (cdr (cdr (car x))))))
     (cddddr . (lambda (x) (cdr (cdr (cdr (cdr x))))))
     (list . (lambda a a))
     (list? . (λ (x) (or (eq? x '())
                         (and (pair? x)
                              (list? (cdr x))))))
     (length .
             (lambda (a)
               (let loop ((a a) (len 0))
                 (if (null? a)
                     len
                     (loop (cdr a) (add1 len))))))
     (append .
             (lambda a
               (letrec ((app2 (lambda (a b)
                                (if (null? a)
                                    b
                                    (cons (car a) (app2 (cdr a) b))))))
                 (let loop ((a a))
                   (cond ((null? a) '())
                         ((null? (cdr a)) (car a))
                         (else (app2 (car a) (loop (cdr a)))))))))
     (reverse .
              (lambda (a)
                (let loop ((a a) (acc '()))
                  (if (null? a)
                      acc
                      (loop (cdr a) (cons (car a) acc))))))
     (list-tail .
                (lambda (a n)
                  (if (zero? n)
                      a
                      (list-tail (cdr a) (- n 1)))))
     (list-ref .
               (lambda (a n)
                 (if (zero? n)
                     (car a)
                     (list-ref (cdr a) (- n 1)))))
     (memq .
           (lambda (x a)
             (cond ((null? a) #f)
                   ((eq? x (car a)) a)
                   (else (memq x (cdr a))))))
     (memv .
           (lambda (x a)
             (cond ((null? a) #f)
                   ((eqv? x (car a)) a)
                   (else (memv x (cdr a))))))
     (member .
             (lambda (x a)
               (cond ((null? a) #f)
                     ((equal? x (car a)) a)
                     (else (member x (cdr a))))))
     (assq .
           (lambda (x a)
             (cond ((null? a) #f)
                   ((eq? x (car (car a))) (car a))
                   (else (assq x (cdr a))))))
     (assv .
           (lambda (x a)
             (cond ((null? a) #f)
                   ((eqv? x (car (car a))) (car a))
                   (else (assv x (cdr a))))))
     (assoc .
            (lambda (x a)
              (cond ((null? a) #f)
                    ((equal? x (car (car a))) (car a))
                    (else (assoc x (cdr a))))))
     (string->list .
                   (lambda (s)
                     (let loop ((n (- (string-length s) 1)) (acc '()))
                       (if (negative? n)
                           acc
                           (loop (- n 1) (cons (string-ref s n) acc))))))
                                        ;    (define list->string
                                        ;      (lambda (a)
                                        ;        (apply string a)))
     (list->string .
                   (lambda (a)
                     (define length
                       (lambda (a)
                         (let loop ((a a) (len 0))
                           (if (null? a)
                               len
                               (loop (cdr a) (add1 len))))))
                     (let ((s (make-string (length a))))
                       (let loop ((i 0) (a a))
                         (if (null? a)
                             s
                             (begin
                               (string-set! s i (car a))
                               (loop (add1 i) (cdr a))))))))
     (vector->list .
                   (lambda (v)
                     (let loop ((n (- (vector-length v) 1)) (acc '()))
                       (if (negative? n)
                           acc
                           (loop (- n 1) (cons (vector-ref v n) acc))))))
                                        ;    (define list->vector
                                        ;      (lambda (a)
                                        ;        (apply vector a)))
     (list->vector .
                   (lambda (a)
                     (define length
                       (lambda (a)
                         (let loop ((a a) (len 0))
                           (if (null? a)
                               len
                               (loop (cdr a) (add1 len))))))
                     (if (null? a)
                         (vector)
                         (let ((v (make-vector (length a) (car a))))
                           (let loop ((i 1) (a (cdr a)))
                             (if (null? a)
                                 v
                                 (begin
                                   (vector-set! v i (car a))
                                   (loop (add1 i) (cdr a)))))))))
     (map .
          (lambda (f a . args)
            (letrec ((map1 (lambda (f l)
                             (if (null? l)
                                 '()
                                 (cons (f (car l))
                                       (map1 f (cdr l))))))
                     (map2 (lambda (f l1 l2)
                             (cond ((null? l1)
                                    '())
                                   ((null? l2)
                                    (error 'map "lists differ in length"))
                                   (else
                                    (cons (f (car l1) (car l2))
                                          (map2 f (cdr l1) (cdr l2)))))))
                     (map* (lambda (f l*)
                             (if (null? (car l*))
                                 '()
                                 (cons (let ((l (map1 car l*)))
                                         (if (null? l)
                                             (f)
                                             (apply f l)))
                                       (map* f (map1 cdr l*)))))))
              (cond ((null? args)
                     (map1 f a))
                    ((null? (cdr args))
                     (map2 f a (car args)))
                    (else
                     (map* f (cons a args)))))))

     (for-each .
       (lambda (f a . args)
         (letrec ((map (lambda (f l)
                         (if (null? l)
                             '()
                             (cons (f (car l))
                                   (map f (cdr l)))))))
           (letrec ((for-each1 (lambda (f l)
                                 (if (null? l)
                                     (void)
                                     (begin
                                       (f (car l))
                                       (for-each1 f (cdr l))))))
                    (for-each2 (lambda (f l1 l2)
                                 (cond ((null? l1)
                                        (void))
                                       ((null? l2)
                                        (error 'for-each "lists differ in length"))
                                       (else
                                        (f (car l1) (car l2))
                                        (for-each2 f (cdr l1) (cdr l2))))))
                    (for-each* (lambda (f l*)
                                 (if (null? (car l*))
                                     (void)
                                     (begin
                                       (let ((l (map car l*)))
                                         (if (null? l)
                                             (f)
                                             (apply f l)))
                                       (for-each* f (map cdr l*)))))))
             (cond ((null? args)
                    (for-each1 f a))
                   ((null? (cdr args))
                    (for-each2 f a (car args)))
                   (else
                    (for-each* f (cons a args))))))))
     (call-with-current-continuation .
                                     (lambda (f)
                                       (let/cc x (f x))))
     (call-with-input-file .
       (lambda (s f)
         (let* ((p (open-input-file s))
                (v (f p)))
           (close-input-port p)
           v)))
     (call-with-output-file .
       (lambda (s f)
         (let* ((p (open-output-file s))
                (v (f p)))
           (close-output-port p)
           v)))
     (with-input-from-file .
       (lambda (s f)
                                        ; no way to switch current input in R4RS Scheme
         (error 'with-input-from-file "not supported")
         (f)))
     (with-output-to-file .
       (lambda (s f)
                                        ; no way to switch current output in R4RS Scheme
         (error 'with-output-to-file "not supported")
         (f)))     
     (apply .
       (lambda (f arg0 . args)
         (cond [(null? args)
                (cond [(null? arg0) (f)]
                      [(null? (cdr arg0)) (f (car m))]
                      [(null? (cdr (cdr arg0))) (f (car m) (car (cdr m)))]
                      [else (,internal-apply$ f arg0)])]
               [else (,internal-apply$ f (cons arg0 args))])))
       (make-promise .
                     (lambda (thunk)
                       (let ([first #t]
                             [val #f])
                         (lambda ()
                           (cond [(eq? first 'forcing) (error 'force "recursive force")]
                                 [first (set! first 'forcing)
                                        (set! val (thunk))
                                        (set! first #f)
                                        val]
                                 [else val])))))
       (force . (lambda (promise) (promise)))
       (make-list .
                  (lambda (n val)
                    (let loop ((n n))
                      (if (< n 1)
                          '()
                          (cons val (loop (- n 1)))))))
       #;
       (define andmap
         (lambda (f list0 . lists)
           (if (null? list0)
               (and)
               (let loop ((lists (cons list0 lists)))
                 (if (null? (cdr (car lists)))
                     (apply f (map car lists))
                     (and (apply f (map car lists))
                          (loop (map cdr lists))))))))
       #;
       (define ormap
         (lambda (f list0 . lists)
           (if (null? list0)
               (or)
               (let loop ((lists (cons list0 lists)))
                 (if (null? (cdr (car lists)))
                     (apply f (map car lists))
                     (or (apply f (map car lists))
                         (loop (map cdr lists))))))))
       (call/cc .
                (lambda (f)
                  (let/cc x (f x))))
       (dynamic-wind .
           (lambda (in doit out)
             (let* ([a (in)]
                    [b (doit)]
                    [c (out)])
               b)))
       (sort .
             (lambda (compare in)
               in))
       (hash-ref . (λ (h k . rest)
                    (if (null? rest)
                        (core-hash-ref h k)
                        (if (hash-has-key? h k)
                            (core-hash-ref h k)
                            (let ([fail (car rest)])
                              (if (procedure? fail)
                                  (fail)
                                  fail))))))
       (hash-ref! . (λ (h k . rest)
                     (if (immutable? h)
                         (error "Shouldn'ta done that, Bill")
                         (if (null? rest)
                             (core-hash-ref h k)
                             (if (hash-has-key? h k)
                                 (core-hash-ref h k)
                                 (let ([fail (car rest)])
                                   (let ([v (if (procedure? fail)
                                                (fail)
                                                fail)])
                                     (hash-set! h k v)
                                     v)))))))
       )))

(define (add-lib expr renaming fresh-label! fresh-variable!)
  (define fv-raw (free expr))
  (define rename-rev (hash-reverse renaming))
  (define ((fresh-upto var) x)
    (if (eq? x var)
        (hash-ref renaming x)
        (fresh-variable! x)))
  ;; maps the fresh name to the meaning.
  (define-values (prims prim-defs)
    (for*/lists (prims prim-defs)
        ([v (in-set fv-raw)]
         [primv (in-value (hash-ref rename-rev v))]
         [def (in-value (hash-ref r4rs-prims primv
                                  (λ () (error 'add-lib "Unsupported ~a" primv))))])
      ;; in order for the primitive references to match up between expr and the
      ;; parsed meaning, we finagle the meaning of fresh-variable.
      (define-values (d _) (parse def fresh-label! (fresh-upto primv)))
      (values v d)))
  (if (null? prims)
      expr
      ;; close the program
      (lrc (fresh-label!) #t prims prim-defs expr)))