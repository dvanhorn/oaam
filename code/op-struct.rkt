#lang racket
(require (for-syntax racket/syntax
                     syntax/parse
                     syntax/id-table
                     racket/match
                     syntax/struct
                     racket/struct-info))
(provide mk-op-struct)

(begin-for-syntax
 (define (populate fs #:values [vals #f] #:table [table #f])
   (define start (or table (make-free-id-table)))
   (for ([f (in-list fs)]
         [v (if vals (in-list vals) (in-cycle (in-value #t)))])
     (free-id-table-set! start f v))
   start)
 (struct op-struct (transformer container-info fields subfields implicit-fields implicit-params)
         #:property prop:procedure (struct-field-index transformer)
         #:property prop:struct-info (λ (s) (op-struct-container-info s))))

;; Specialize representations
(define-syntax mk-op-struct
  (syntax-parser
    [(_ name:id (~optional parent:id) (fields:id ...) (subfields:id ...)
        (~optional (~seq #:implicit ([impfields:id impparam:id] ...))
                   #:defaults ([(impfields 1) '()]
                               [(impparam 1) '()]))
        (~do (define fieldsl (syntax->list #'(fields ...)))
             (define subfieldsl (syntax->list #'(subfields ...)))
             (define impfieldsl (syntax->list #'(impfields ...)))
             (define fs (populate fieldsl))
             (define sfs (populate subfieldsl))
             (define ifs (populate impfieldsl #:values (attribute impparam)))
             (define parent-info (and (attribute parent) (syntax-local-value #'parent)))
             (define-values (parent-fields
                             all-subfields
                             all-implicits)
               (if parent-info
                   (values
                    (map syntax-local-introduce (op-struct-fields parent-info))
                    (append (map syntax-local-introduce (op-struct-subfields parent-info)) subfieldsl)
                    (populate (map syntax-local-introduce (op-struct-implicit-fields parent-info))
                              #:values (map syntax-local-introduce (op-struct-implicit-params parent-info))
                              #:table ifs))
                   (values '() subfieldsl ifs)))
             (define pfs (populate parent-fields)))
        (~fail #:unless (for/and ([s (in-list subfieldsl)])
                          (free-id-table-ref fs s #f))
               "subfields should be contained in fields list.")
        (~fail #:unless (for/and ([i (in-list impfieldsl)])
                          (free-id-table-ref fs i #f))
               "implicit fields should be contained in fields list")
        (~bind [container (format-id #'name "~a-container" #'name)]
               [(impsub 1) (for/list ([s (in-list all-subfields)])
                             (free-id-table-ref ifs s s))]
               [(allfields 1) (append parent-fields fieldsl)]
               [(exfields 1) (for/list ([f (in-list (attribute allfields))]
                                        #:unless (free-id-table-ref all-implicits f #f))
                               f)])
        (~or
         (~optional (~seq #:expander
                          (~or (~and #:with-first-cons
                                     (~bind [expander
                                             #`(syntax-rules ()
                                                 [(_ fσ #,@(cdr (syntax->list #'(allfields ...))))
                                                  (cons fσ (container #,@all-subfields))])]))
                               expander:expr)) ;; want a different match expander?
                    #:defaults ([expander
                                 #`(syntax-rules ()
                                     [(_ allfields ...)
                                      (container #,@all-subfields)])]))
         (~optional (~seq #:expander-id name-ex:id)
                    #:defaults ([name-ex (format-id #'name "~a:" #'name)]))) ...)
     #:do [(match-define (list-rest _ _ name? sels)
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
     (with-syntax ([((good real-good) ...) good-sels]
                   [(bad ...) bad-sels])
       #`(begin (struct container #,@(if (attribute parent)
                                         (list (format-id #'parent "~a-container" #'parent))
                                         #'())
                        (subfields ...) #:prefab)
                (define-syntax name
                  (op-struct
                   (λ (syn)
                      (syntax-parse syn
                        [(_ exfields ...) #'(container impsub ...)]
                        [n:id (raise-syntax-error #f "Not first class" syn)]))
                   (extract-struct-info (syntax-local-value #'container))
                   (list #'fields ...)
                   (list #'subfields ...)
                   (list #'impfields ...)
                   (list #'impparam ...)))
                (define #,name? #,real-name?)
                (define good real-good) ...
                ;; Make sure things compile but I get good error messages
                ;; if I have runtime logic errors.
                (define (bad . rest)
                  (error 'bad "Not present in specialized representation")) ...
                (define-match-expander name-ex expander)))]))