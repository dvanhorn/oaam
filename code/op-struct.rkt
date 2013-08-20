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
 (define (stx->datum stx)
   (match stx
     ['() '()]
     [(cons stx stxs)
      (cons (stx->datum stx) (stx->datum stxs))]
     [(? syntax?) (syntax->datum stx)]))
 (define (populate fs #:values [vals #f] #:table [table #f])
   (define start (or table (make-free-id-table)))
   (for ([f (in-list fs)]
         [v (if vals (in-list vals) (in-cycle (in-value #t)))])
     (free-id-table-set! start f v))
   start)
 (struct op-struct (transformer container-info fields subfields implicit-fields implicit-params)
         #:property prop:procedure (struct-field-index transformer)
         #:property prop:struct-info (λ (s) (op-struct-container-info s)))
 (define (split-get/sets lst)
   (match lst
     ['() (values '() '())]
     [(list-rest get set rest)
      (define-values (gets sets) (split-get/sets rest))
      (values (cons get gets) (cons set sets))]))
 (define (split-good/bad fields sfs accessors real-accessors)
   (for/fold ([good '()] [bad '()]) ([f (in-list fields)]
                                     [acc (in-list accessors)]
                                     [real (in-list real-accessors)])
     ;; Supposed field is actually present. Pair the container's
     ;; accessor with the desired accessor name.
     (cond [(free-id-table-ref sfs f #f)
            (values `((,acc ,real) . ,good) bad)]
           [else (values good (cons acc bad))])))
 (define-syntax-class field-spec
   #:attributes (field kinds clause)
   #:description "Specificiation for struct field"
   (pattern field:id #:with clause #'field #:attr kinds '())
   (pattern (~and [field:id (~or #:mutable #:auto ;; FIXME: better way to express?
                                 (~seq (~or (~once #:mutable) (~once #:auto)) ...))]
                  clause)
            #:attr kinds (stx->datum (cdr (syntax->list #'clause))))))

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
             (define f-attrs (populate fieldsl #:values (map cons
                                                             (syntax->list #'(flds.clause ...))
                                                             (attribute flds.kinds))))
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
             (define-values (tail-implicits tail-subimplicits)
               (cond
                [(attribute tail)
                 (define tail-op (syntax-local-value #'tail))
                 (define tls (populate (op-struct-subfields tail-op)))
                 (define implicits (op-struct-implicit-fields tail-op))
                 (values implicits
                         (for/list ([f (in-list implicits)]
                                    #:when (free-id-table-ref tls f #f))
                           f))]
                [else (values '() '())]))
             (define all-fields (append (if (attribute tail)
                                            (drop-right parent-fields 1)
                                            parent-fields)
                                        tail-implicits
                                        fieldsl))
             (define all-subfields (append (if (attribute tail)
                                               (drop-right all-parent-subfields 1)
                                               all-parent-subfields)
                                           tail-subimplicits
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
     #:do [(match-define (list-rest _ _ name? get/sets)
                         (build-struct-names #'name fieldsl #f #f #'name))
           (match-define (list-rest _ _ real-name? real-get/sets)
                         (build-struct-names #'container fieldsl #f #f #'container))
           (define-values (sels sets) (split-get/sets get/sets))
           (define-values (real-sels real-sets) (split-get/sets real-get/sets))
           (define-values (good-sels bad-sels) (split-good/bad fieldsl sfs sels real-sels))
           ;; Remove immutable fields from subfields table now that we only need it
           ;; to create the setters.
           (for ([f (in-list subfieldsl)]
                 #:unless (memv '#:mutable (cdr (free-id-table-ref f-attrs f (cons #f '())))))
             (free-id-table-set! sfs f #f))
           (define-values (good-sets bad-sets) (split-good/bad fieldsl sfs sets real-sets))]
     (with-syntax ([((goodg real-goodg) ...) good-sels]
                   [((goods real-goods) ...) good-sets]
                   [(badg ...) bad-sels]
                   [(bads ...) bad-sets]
                   [(subfields-attr ...)
                    (for/list ([s (in-list subfieldsl)])
                      (car (free-id-table-ref f-attrs s)))]
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
                (define goodg real-goodg) ...
                (define goods real-goods) ...
                ;; Make sure things compile but I get good error messages
                ;; if I have runtime logic errors.
                (define (bads . rest)
                  (error 'bads "Not present in specialized representation")) ...
                (define (badg . rest)
                  (error 'badg "Not present in specialized representation")) ...
                (define-match-expander name-ex expander)))]))