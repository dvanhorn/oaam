#lang racket
(require (for-syntax racket/syntax
                     syntax/parse
                     racket/list
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
         #:property prop:struct-info (λ (s) (op-struct-container-info s)))
 (define-syntax-class field-spec
   #:attributes (field clause)
   #:description "Specificiation for struct field"
   (pattern field:id #:with clause #'field)
   (pattern (~and [field:id (~or #:mutable #:auto)] clause))))

;; Specialize representations
(define-syntax mk-op-struct
  (syntax-parser
    [(_ name:id (~or (~optional parent:id)
                     (~optional (parent:id tail:id (~optional (~seq #:exp tailm:id)))))
        (flds:field-spec ...)
        (subfields:id ...)
        (~optional (~seq #:implicit ([impfields:id impparam:id] ...))
                   #:defaults ([(impfields 1) '()]
                               [(impparam 1) '()]))
        (~do (define fieldsl (syntax->list #'(flds.field ...)))
             (define subfieldsl (syntax->list #'(subfields ...)))
             (define impfieldsl (syntax->list #'(impfields ...)))
             (define fs (populate fieldsl))
             (define sfs (populate subfieldsl))
             (define ifs (populate impfieldsl #:values (attribute impparam)))
             (define f-attrs (populate fieldsl #:values (syntax->list #'(flds.clause ...))))
             (define parent-info (and (attribute parent) (syntax-local-value #'parent)))
             (define-values (parent-fields
                             all-parent-subfields
                             all-implicits)
               (let ancestors ([parent-info parent-info]
                               [parent-fields '()]
                               [all-parent-subfields '()]
                               [all-implicits ifs])
                (cond [(op-struct? parent-info)
                       (define parent-parent (list-ref (op-struct-container-info parent-info) 5))
                       (ancestors
                        (and (identifier? parent-parent)
                             (syntax-local-value (syntax-local-introduce parent-parent) (λ () #f)))
                        (append (map syntax-local-introduce (op-struct-fields parent-info)) parent-fields)
                        (append (map syntax-local-introduce (op-struct-subfields parent-info)) all-parent-subfields)
                        (populate (map syntax-local-introduce (op-struct-implicit-fields parent-info))
                                  #:values (map syntax-local-introduce (op-struct-implicit-params parent-info))
                                  #:table all-implicits))]
                      [else (values parent-fields all-parent-subfields all-implicits)])))
             (define tail-implicits
               (if (attribute tail)
                   (op-struct-implicit-fields (syntax-local-value #'tail))
                   '()))
             (define all-fields (append (if (attribute tail)
                                            (drop-right parent-fields 1)
                                            parent-fields)
                                        tail-implicits
                                        fieldsl))
             (define all-subfields (append (if (attribute tail)
                                               (drop-right all-parent-subfields 1)
                                               all-parent-subfields)
                                           tail-implicits
                                           subfieldsl))
             (define/with-syntax tail:
               (cond [(attribute tailm) #'tailm]
                     [(attribute tail) (format-id #'tail "~a:" #'tail)]
                     [else #'ignore])))
        (~fail #:unless (for/and ([s (in-list subfieldsl)])
                          (free-id-table-ref fs s #f))
               "subfields should be contained in fields list.")
        (~fail #:unless (for/and ([i (in-list impfieldsl)])
                          (free-id-table-ref fs i #f))
               "implicit fields should be contained in fields list")
        (~bind [container (format-id #'name "~a-container" #'name)]
               [(allfields 1) all-fields]
               [(impsub 1) (for/list ([s (in-list subfieldsl)])
                             (free-id-table-ref ifs s s))]
               [(impallsub 1) (for/list ([s (in-list all-subfields)])
                             (free-id-table-ref ifs s s))]
               ;; explicit parent fields
               [(expfields 1) (let ([lst
                                     (for/list ([f (in-list parent-fields)]
                                                #:unless (free-id-table-ref all-implicits f #f))
                                       f)])
                                (if (attribute tail)
                                    (drop-right lst 1)
                                    lst))]
               ;; explicit current fields
               [(exfields 1) (for/list ([f (in-list fieldsl)]
                                        #:unless (free-id-table-ref all-implicits f #f))
                               f)])
        (~or
         (~optional (~seq #:expander
                          (~or (~and #:with-first-cons
                                     (~bind [expander
                                             #`(syntax-rules ()
                                                 [(_ fσ #,@(cdr (syntax->list #'(allfields ...))))
                                                  #,(if (attribute tail)
                                                        #`(cons fσ
                                                                (parent #,@(drop-right all-parent-subfields 1)
                                                                        (tail: #,@tail-implicits
                                                                               (container #,@subfieldsl))))
                                                        #`(cons fσ (container #,@all-subfields)))])]))
                               expander:expr)) ;; want a different match expander?
                    #:defaults ([expander
                                 #`(syntax-rules ()
                                     [(_ allfields ...)
                                      #,(if (attribute tail)
                                            #`(parent #,@(drop-right all-parent-subfields 1)
                                                      (tail: #,@tail-implicits (container #,@subfieldsl)))
                                            #`(container #,@all-subfields))])]))
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
                   [(bad ...) bad-sels]
                   [(subfields-attr ...)
                    (for/list ([s (in-list subfieldsl)])
                      (free-id-table-ref f-attrs s))]
                   [transformer
                    #`(λ (syn)
                         (syntax-parse syn
                           [(_ expfields ... exfields ...)
                            #,(if (attribute tail)
                                  ;; implicits are added by parent and tail syntaxes.
                                  #'#`(parent expfields ... (tail (container impsub ...)))
                                  #'#'(container impallsub ...))]
                           [n:id (raise-syntax-error #f "Not first class" syn)]))])
       #`(begin (struct container #,@(if (and (attribute parent) (not (attribute tail)))
                                         (list #'parent)
                                         #'())
                        (subfields-attr ...) #:prefab)
                (define-syntax name
                  (op-struct
                   transformer
                   (extract-struct-info (syntax-local-value #'container))
                   (list #'flds.field ...)
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