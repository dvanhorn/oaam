#lang racket
(require (for-syntax racket/syntax
                     syntax/parse
                     syntax/id-table
                     racket/match
                     syntax/struct))
(provide mk-op-struct)

;; Specialize representations
(define-syntax mk-op-struct
  (syntax-parser
    [(_ name:id (fields:id ...) (subfields:id ...)
        (~bind [container (format-id #'name "~a-container" #'name)])
        (~or
         (~optional (~seq #:expander
                          (~or (~and #:with-first-cons
                                     (~bind [expander
                                             #`(syntax-rules ()
                                                 [(_ σ #,@(cdr (syntax->list #'(fields ...))))
                                                  (cons σ (container subfields ...))])]))
                               expander:expr)) ;; want a different match expander?
                    #:defaults ([expander
                                 #'(syntax-rules ()
                                     [(_ fields ...)
                                      (container subfields ...)])]))
         (~optional (~seq #:expander-id name-ex:id)
                    #:defaults ([name-ex (format-id #'name "~a:" #'name)]))) ...)
     #:do [(define (populate fs)
             (let ([start (make-free-id-table)])
               (for ([f (in-list fs)]) (free-id-table-set! start f #t))
               start))
           (define fieldsl (syntax->list #'(fields ...)))
           (define subfieldsl (syntax->list #'(subfields ...)))
           (define fs (populate fieldsl))
           (define sfs (populate subfieldsl))
           (match-define (list-rest _ _ name? sels)
                         (build-struct-names #'name fieldsl #f #t #'name))
           (match-define (list-rest _ _ real-name? real-sels)
                         (build-struct-names #'container fieldsl #f #t #'container))
           (define-values (good-sels bad-sels)
             (for/fold ([good '()] [bad '()]) ([f (in-list fieldsl)]
                                               [sel (in-list sels)]
                                               [real (in-list real-sels)])
               ;; Supposed field is actually present. Pair the container's
               ;; selector with the desired selector name.
               (cond [(free-id-table-ref sfs f #f)
                      (values `((,sel ,real) . ,good) bad)]
                     [else (values good (cons sel bad))])))]
     #:fail-unless (for/and ([s (in-list subfieldsl)])
                     (free-id-table-ref fs s #f))
     "Subfields should be contained in fields list."
     (with-syntax ([((good real-good) ...) good-sels]
                   [(bad ...) bad-sels])
     #`(begin (struct container (subfields ...) #:prefab)
              (define-syntax (name syn)
                (syntax-parse syn
                  [(_ fields ...) #'(container subfields ...)]
                  [n:id (raise-syntax-error #f "Not first class" syn)]))
              (define #,name? #,real-name?)
              (define good real-good) ...
              ;; Make sure things compile but I get good error messages
              ;; if I have runtime logic errors.
              (define (bad . rest)
                (error 'bad "Not present in specialized representation")) ...
              (define-match-expander name-ex expander)))]))