#lang racket

(require "data.rkt")
(provide mk-prim-meaning)

(define-for-syntax ((mk-mk-prim-meaning just-types?) stx)
  (syntax-case stx ()
    [(_ getter setter widen)
     #`(#,(if just-types?
            #'(...
               (define-syntax-rule (define-types defines ... ([prim store? meaning type] ...))
                '((prim . type) ...)))
            #'(...
               (define-syntax-rule (define-types defines ... ([prim store? meaning type] ...))
                (let ()
                  defines ...
                  (hasheq (list (list* 'prim store? meaning 'type) ...))))))
        (define-types
          (define both '(#t #f))
          (define (equalv? v0 v1)
            (match* (v0 v1)
              [((? clos?) _) (and (clos? v1) both)] ;; FIXME: not right for concrete
              [(_ (? clos?)) #f] ;; first not a closure
              [((? consv?) _) (and (consv? v1) both)] ;; FIXME: not right for concrete
              [(_ (? consv?)) #f] ;; first not a cons
              [((? vectorv?) _) (and (vectorv? v1) both)] ;; FIXME: not right for concrete
              [(_ (? vectorv?)) #f] ;; first not a vector
              [((? primop?) _) (equal? v0 v1)]
              [(_ (? primop?)) #f] ;; first not a primop
              [((? number?) _) (cond [(eq? 'number v1) both]
                                     [(number? v1) (= v0 v1)]
                                     [else #f])]
              [(_ (? number?)) (cond [(eq? 'number v0) both]
                                     [else #f])] ;; first not a number
              [('number _) (and (eq? 'number v1) both)]
              [(_ 'number) #f]
              [((? string?) _) (cond [(eq? 'string v1) both]
                                     [(string? v1) (string=? v0 v1)]
                                     [else #f])]
              [(_ (? string?)) (cond [(eq? 'string v0) both]
                                     [else #f])] ;; first not a string
              [('string _) (and (eq? 'string v1) both)]
              [(_ 'string) #f]
              [((? symbol?) _) (cond [(eq? 'symbol v1) both]
                                     [(symbol? v1) (eq? v0 v1)]
                                     [else #f])]
              [(_ (? symbol?)) (cond [(eq? 'symbol v0) both]
                                     [else #f])] ;; first not a symbol
              [('symbol _) (and (eq? 'symbol v1) both)]
              [((? boolean?) _) (equal? v0 v1)]
              [('() _) (eq? '() v1)]
              [(_ '()) #f]
              [((? void?) _) (void? v1)]
              [(_ (? void?)) #f]
              [(_ _) (error 'equalv? "Incomplete match ~a ~a" v0 v1)]))
          (define (vectorv-ref vec z)
            (match vec
              [(vectorv _ '()) stuck]
              [(vectorv _ (? list? l))
               ;; sloppy. Abstract ref could get stuck, but just join all addrs.
               (cond [(eq? 'number z)
                      (error 'vectorv-ref "Abstract vectors should have a single cell")]
                     [(or (< z 0) (>= z (length l))) stuck]
                     [else (getter (list-ref l z))])]
              [(vectorv _ abs-cell) (getter abs-cell)]))
          (define (vectorv-set! vec i val)
            (match vec
              [(vectorv _ '()) stuck]
              [(vectorv _ (? list? l))
               (cond [(eq? 'number i)
                      (error 'vectorv-set! "Abstract vectors should have a single cell")]
                     [(or (< z 0) (>= z (length l))) stuck]
                     [else (setter (list-ref l i) val)])]
              [(vectorv _ abs-cell) (setter abs-cell val)]))
          (define (add1v n)
            (if (eq? 'number n)
              'number
              (widen (add1 n))))
          (define (sub1v n)
            (if (eq? 'number n)
              'number
              (widen (sub1 n))))
          (define (zero?v n)
            (if (eq? 'number n)
              both
              (zero? n)))
          ((add1        #f add1v        (z -> z))
           (sub1        #f sub1v        (z -> z))
           (zero?       #f zero?v       (z -> b))
           (not         #f not          (any -> b))
           (*           #f *            (z z -> z))
           (+           #f +            (z z -> z))
           (-           #f -            (z z -> z))
           (=           #f =            (z z -> b))
           (equal?      #f equalv?      (any any -> b))
           (eqv?        #f equalv?      (any any -> b))
           (eq?         #f equalv?      (any any -> b))
           (vector?     #f vectorv?     (any -> b))
           (pair?       #f consv?       (any -> b))
           (vector-ref  #t vectorv-ref  (v z -> any))
           (vector-set! #t vectorv-set! (v z any -> !)))))]))
(define-syntax mk-primitives (mk-mk-prim-meaning #t))
(define prim-types (mk-primitives _ _ _))
(define prims (hash-keys prim-types))
(define (primitive? x) (memq x prims))
(define (split-types t)
  (define-values (rdom rrng _)
    (for/fold ([rdom '()] [rrng '()] [in-rng? #f])
        ([s (in-list t)])
      (cond [(eq? s '->) (values rdom rrng #t)]
            [in-rng? (values rdom (cons s rrng) #t)]
            [else (values (cons s rdom) rrng)])))
  (values (reverse rdom) (reverse rrng)))

(define (type-match t v)
  (case t
    [(z) (or (number? v) (eq? v 'number))]
    [(s) (or (string? v) (eq? v 'string))]
    [(!) (void? v)]
    [(b) (boolean? v)]
    [(v) (vectorv? v)]
    [(p) (consv? v)]
    [(any) #t]))

(define (vs-match-dom dom vs)
  (and (= (length dom) (length vs))
       (for/and ([t (in-list dom)]
                 [v (in-list vs)])
         (type-match t v))))

(define-syntax-rule (mk-error-or-dispatch error-or-dispatch prim-meaning)
  (define-syntax-rule (error-or-dispatch o vs)
    (cond [(vs-match-dom (hash-ref prim-types o) vs)
           (prim-meaning o vs)]
          [else stuck])))
(provide mk-error-or-dispatch
         primitive?
         mk-mk-prim-meaning)
