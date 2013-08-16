#lang racket/base
(require racket/match
         (for-syntax racket/base
                     syntax/parse racket/syntax racket/struct-info
                     racket/list
                     racket/pretty))
(provide struct-copy/inherit)

(define-syntax (struct-copy/inherit stx)
  (syntax-parse stx
    [(_ parent:id (children:id ...) struct-e:expr [field:id f-e:expr] ...)
     #:do [(define parent-v (syntax-local-value #'parent))
           (define childrenl (syntax->list #'(children ...)))
           (define children-v (map syntax-local-value childrenl))
           (define bad-children (filter-not struct-info? children-v))]
     #:fail-unless (struct-info? parent-v)
     (format "No struct-info attached to parent ~a" #'parent)
     #:fail-unless (null? bad-children)
     (format "No struct-info attached to children ~a" bad-children)
     #:do [(define parent-info (extract-struct-info parent-v))
           (pretty-print parent-info)
           (define children-parents (reverse
                                     (for/fold ([acc '()]) ([c (in-list children-v)]
                                                            [c-id (in-list childrenl)])
                                       (define super (list-ref (extract-struct-info c) 5))
                                       (if (free-identifier=? super #'parent)
                                           acc
                                           (cons c-id acc)))))]
     #:fail-unless (null? children-parents)
     (format "Children do not have ~a as a parent: ~a" #'parent children-parents)
     (with-syntax ([(children? ...) (map (λ (x) (format-id x "~a?" x)) (syntax->list #'(children ...)))])
      #'(let ([v struct-e]
              [field f-e] ...)
          (match v
            [(? children?) (struct-copy children v [field #:parent parent field] ...)]
            ...)))]))

(module+ test
  (require rackunit)
  (struct a (x) #:transparent)
  (struct b a (y) #:transparent)
  (struct c b (z))
  (check equal?
         (b 1 2)
         (struct-copy/inherit a (b) (b 0 2) [x 1])))