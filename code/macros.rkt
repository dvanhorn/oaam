#lang racket

(require (for-syntax racket/syntax) "data.rkt")
(provide macro-env define-ctx-tf
         igensym
         void$ quote$
         special kwote define-ctx)

(define-nonce special)
(define-nonce define-ctx)
(define-nonce kwote)
;; Directives to make special abstract data from "large" literals.
(define-syntax (mk-specials stx)
  (syntax-case stx ()
    [(_  names ...)
     (with-syntax ([(names$ ...) (map (λ (i) (format-id i "~a$" i)) (syntax->list #'(names ...)))])
       #'(begin (define names$ (cons special 'names)) ...))]))
(mk-specials begin car cdr cons let letrec lambda if eq? or quote void not vector
             qlist^ qimproper^ qvector^ qhash^)

(define (igensym [start 'g]) (string->symbol (symbol->string (gensym start))))

(define ((rename-tf to) inp) (cons to inp))

(define (quote-tf inp)
  (define limit (cons-limit))
  (define (improper-length l)
    (cond [(pair? l) (add1 (improper-length (cdr l)))]
          [else 0]))
  (define (split-improper l)
    (let loop ([l l] [front '()])
      (cond [(pair? l) (loop (cdr l) (cons (car l) front))]
            [else (values front l)])))
  (match inp
    [`(quote ,d)
     (let loop ([d d])
       (cond [(atomic? d) `(,kwote ,d)]
             [(list? d)
              (if (< (length d) limit)
                  `(,cons$ ,(loop (car d)) ,(loop (cdr d)))
                  `(,qlist^$ . ,(map loop d)))]             
             ;; List literals get exploded into conses
             [(pair? d)
              (cond [(< (improper-length d) limit)
                     `(,cons$ ,(loop (car d)) ,(loop (car d)))]
                    [else (define-values (front last) (split-improper d))
                          `(,qimproper^$ (loop last) . ,(map loop front))])]
             [(vector? d)
              (cond [(< (vector-length d) limit)
                     `(,kwote ,d)]
                    [else `(,qvector^$ . ,(map loop (vector->list d)))])]
             [(hash? d)
              (cond [(< (hash-count d) limit) `(,kwote ,d)]
                    ;; qhash^ k v k v k v ... ....
                    [else `(,qhash^$ . 
                                     ,(append-map
                                       (match-lambda [(cons k v) (list (loop k) (loop v))])
                                       (hash->list d)))])]
             [else (error 'parse "Unsupported datum ~a" d)]))]
    [_ (error 'quote-tf "Bad input ~a" inp)]))

(module+ test
  (require rackunit)
  (check equal? (quote-tf '(quote (0 1 2 3 4 5 6 7 8 9)))
         `(,qlist^$ (,kwote 0) (,kwote 1) (,kwote 2) (,kwote 3) (,kwote 4) (,kwote 5)
                    (,kwote 6) (,kwote 7) (,kwote 8) (,kwote 9))))

(define (begin-tf inp)
  (match inp
    [`(begin ,e) e]
    [`(begin ,e . ,es) `((,lambda$ (,(igensym)) ,(begin-tf `(begin . ,es))) ,e)]
    ['(begin) (error 'begin-tf "Expected at least one expression")]
    [_ (error 'begin-tf "Bad input ~a" inp)]))

(define (let-tf inp)
  (match inp
    [`(let () . ,b) `(,define-ctx . ,b)]
    [`(let ([,xs ,es] ...) . ,b)
     `((,lambda$ ,xs . ,b) . ,es)]
    [`(let ,(? symbol? loop) ([,xs ,es] ...) . ,b)
     `(,letrec$ ([,loop (,lambda$ ,xs . ,b)])
         (,loop . ,es))]
    [_ (error 'let-tf "Bad input ~a" inp)]))

(define (let*-tf inp)
  (match inp
    [`(let* () . ,b) `(,define-ctx . ,b)]
    [`(let* ([,x ,e] . ,rest) . ,b)
     `(let ([,x ,e]) ,(let*-tf `(let* ,rest . ,b)))]
    [_ (error 'let*-tf "Bad input ~a" inp)]))

(define (or-tf inp)
  (match inp
    ['(or) #f]
    [`(or ,e) e]
    [`(or ,e . ,es)
     (define x (igensym 'or-temp))
     `(,let$ ([,x ,e]) (,if$ ,x ,x ,(or-tf `(or . ,es))))]))

(define (and-tf inp)
  (match inp
    ['(and) #t]
    [`(and ,e) e]
    [`(and ,e . ,es) `(,if$ ,e ,(and-tf `(and . ,es)) #f)]))

(define (case-tf inp)
  (define x (igensym 'case-tmp))
  (define (xin-datums datums)
    (cons or$ (for/list ([datum (in-list datums)])
                `(,eq?$ ,x (,quote$ ,datum)))))
  (define (tf datumss rhsss lasts)
    (match* (datumss rhsss lasts)
      [('() '() #f) `(,void$)] ;; XXX: needs explicit renaming to be correct
      [('() '() lasts) `(,define-ctx . ,lasts)]
      [((cons datums datumss) (cons rhss rhsss) lasts)
       `(,if$ ,(xin-datums datums)
              (,define-ctx . ,rhss)
              ,(tf datumss rhsss lasts))]))
  (match inp
    [`(case ,in [(,datumss ...) . ,rhsss] ... [else . ,last])
     `(,let$ ([,x ,in]) ,(tf datumss rhsss last))]
    [`(case ,in [(,datumss ...) . ,rhsss] ...)
     `(,let$ ([,x ,in]) ,(tf datumss rhsss #f))]
    [`(case . ,rst) (error 'case-tf "Bad input ~a" rst)]))

;; XXX: improper handling of else and =>. Oh well.
(define (cond-tf inp)
  (match inp
    [`(cond) `(,void$)]
    [`(cond [else . ,lasts]) `(,define-ctx . ,lasts)]
    [`(cond [,guard => ,rhs] . ,rest)
     (define x (igensym 'cond-proc))
     `(,let$ ([,x ,guard])
         (,if$ ,x
               (,rhs ,x)
               ,(cond-tf `(cond . ,rest))))]
    [`(cond [,guard ,rhss ...] . ,rest)
     `(,if$ ,guard (,define-ctx . ,rhss) ,(cond-tf `(cond . ,rest)))]
    [_ (error 'cond-tf "Bad input ~a" inp)]))

(define (define-ctx-tf inp)
  (define (parse-defns ds)
    (match ds
      ['() '()]
      [`((define (,f . ,xs) . ,b) . ,ds)
       (parse-defns `((define ,f (lambda ,xs . ,b)) . ,ds))]
      [`((define ,f ,e) . ,ds)
       (cons (list f e)
             (parse-defns ds))]))
  (match inp
    [(list e) e]
    [(list (and ds `(define ,_ . ,_)) ... es ...)
     (when (null? es)
       (error 'define-ctx "expected at least one expression after defines ~a" inp))
     `(,letrec$ ,(parse-defns ds) (,begin$ ,@es))]))

(define (do-tf inp)
  (let loop ([e (cdr inp)])
    (match e
      ;; (((var init . step) ...) (e0 e1 ...) c ...)
      [(list-rest (? list? vis) (cons e0 (? list? e1)) (? list? c))
       (if (andmap (match-lambda
                    [(list-rest _ _ _) #t]
                    [_ #f])
                   vis)
           (let* ([var (map car vis)]
                  [init (map cadr vis)]
                  [step (map cddr vis)]
                  [step (map (lambda (v s)
                               (match s
                                 [`() v]
                                 [`(,e) e]
                                 [_ (error 'do-tf "invalid do expression ~a" inp)]))
                             var
                             step)])
             (let ([doloop (gensym)])
               (match e1
                 ['()
                  `(,let$ ,doloop ,(map list var init)
                          (,if$ (,not$ ,e0)
                                (,begin$ ,@c (,doloop ,@step) (void))
                                (,void$)))]
                 [(list body0 body ...)
                  `(,let$ ,doloop ,(map list var init)
                        (,if$ ,e0
                            (,begin$ ,body0 ,@body)
                            (,begin$ ,@c (,doloop ,@step))))]
                 [_ (error 'do-tf "invalid do expression ~a" inp)])))
           (error 'do-tf "invalid do expression ~a" inp))]
      (_ (error 'do-tf "invalid do expression ~a" inp)))))

(define (unless-tf inp)
  (match inp
    [`(unless ,guard . ,body)
     `(if ,guard (,void$) (,define-ctx . ,body))]))

(define macro-env
  (hasheq 'quote quote-tf
          'begin begin-tf
          'do do-tf
          'or or-tf
          'and and-tf
          'case case-tf
          'cond cond-tf
          'let let-tf
          'let* let*-tf
          'unless unless-tf
          'λ (rename-tf 'lambda)
          'letrec* (rename-tf 'letrec)))
