#lang racket
(require (for-syntax racket/syntax
                     syntax/parse
                     syntax/parse/experimental/template
                     syntax/id-table
                     racket/match
                     syntax/struct
                     racket/trace)
         racket/stxparam)
(provide mk-op-struct)

;; Map struct names to (container, given fields, actual subfields, represented subfields)
(define-for-syntax optional (make-free-id-table #:phase -1))
#;
(define-for-syntax (get-op id)
  (define res #f)
  (free-id-table-for-each optional (λ (id* v) (when (free-identifier=? id id*)
                                                (set! res v))))
  res)

(define-for-syntax (get-op id)
  (free-id-table-ref optional id
                     (λ ()
                        (printf "Bad optional~%")
                        (free-id-table-for-each optional (λ (id v) (printf "~a ↦ ~a~%" id v)))
                        (raise-syntax-error #f "Unregistered struct" id))))
(define-for-syntax (safe-cdr lst) (if (pair? lst) (cdr lst) null))
(begin-for-syntax (trace safe-cdr))

;; Specialize representations
(define-syntax (mk-op-struct stx)
  (syntax-parse stx
    [(_ name:id
        (~optional (~and super:id
                         (~bind [(parent-fields 1) (syntax->list (cadr (get-op #'super)))]
                                [(parent-subfields 1) (syntax->list (caddr (get-op #'super)))]
                                [(parent-rfields 1) (cadddr (get-op #'super))]
                                [(super-op 1) (list (car (get-op #'super)))]))
                   #:defaults ([(parent-fields 1) '()]
                               [(parent-subfields 1) '()]
                               [(parent-rfields 1) '()]
                               [(super-op 1) '()]))
        (fields:id ...)
        (~optional (subfields:id ...)
                   #:defaults ([(subfields 1) (syntax->list #'(fields ...))]))
        (~bind [container (format-id #'name "~a-container" #'name)])
        (~or
         (~optional
          (~seq #:expander
                (~or
                 (~and #:with-first-cons
                       (~bind [expander
                               #`(λ (stx)
                                    (syntax-case stx ()
                                      [(_ fσ
                                          #,@(safe-cdr (syntax->list #'(parent-fields ...)))
                                          fields ...)
                                       #'(list-rest fσ parent-subfields ...
                                                    (container subfields ...))]
                                      [_ (raise-syntax-error #f "Bad cons matcher" stx)]))]))
                     expander:expr)) ;; want a different match expander?
                    #:defaults ([expander
                                 #'(λ (stx)
                                      (syntax-case stx ()
                                        [(_ parent-fields ... fields ...)
                                         #'(container parent-subfields ... subfields ...)]
                                        [_ (raise-syntax-error #f "Bad default matcher" stx)]))]))
         (~optional (~seq #:expander-id name-ex:id)
                    #:defaults ([name-ex (format-id #'name "~a:" #'name)]))
         ;; Extras in states really should be hidden from the main semantics.
         ;; We use syntax parameters and make constructors automatically pass
         ;; the parameter in the right position.
         (~optional (~seq #:fields-as-parameters (param-fields ...))
                    #:defaults ([(param-fields 1) '()]))) ...)
     #:do [(define (populate fs)
             (let ([start (make-free-id-table)])
               (for ([f (in-list fs)]) (free-id-table-set! start f #t))
               start))
           (define fieldsl (syntax->list #'(fields ...)))
           (define subfieldsl (syntax->list #'(subfields ...)))
           (define pfieldsl (syntax->list #'(param-fields ...)))
           (define fs (populate fieldsl))
           (define sfs (populate subfieldsl))
           (define pfs (populate pfieldsl))
           (match-define (list-rest _ _ name? sels)
                         (build-struct-names #'name fieldsl #f #t #'name))
           (match-define (list-rest _ _ real-name? real-sels)
                         (build-struct-names #'container fieldsl #f #t #'container))
           (define-values (good-sels bad-sels rev-rep-fields)
             (for/fold ([good '()] [bad '()] [rep-fields '()])
                 ([f (in-list fieldsl)]
                  [sel (in-list sels)]
                  [real (in-list real-sels)])
               (define rep-field
                 (cond [(free-id-table-ref pfs f #f) rep-fields]
                       [else (cons f rep-fields)]))
               ;; Supposed field is actually present. Pair the container's
               ;; selector with the desired selector name.
               (cond [(free-id-table-ref sfs f #f)
                      (values `((,sel ,real) . ,good) bad rep-field)]
                     [else (values good (cons sel bad) rep-field)])))]
     #:fail-unless (for/and ([s (in-list subfieldsl)])
                     (free-id-table-ref fs s #f))
     "Subfields should be contained in fields list."
     #:fail-unless (for/and ([s (in-list pfieldsl)])
                     (free-id-table-ref sfs s #f))
     "Parameter fields should be contained in subfields list."
     (define super-info (and (attribute super)
                             (get-op #'super)))
     (define rfields (reverse rev-rep-fields))
     ;; Note fields for later use (only allows single parent depth for now)
     (free-id-table-set! optional #'name (list #'container
                                               #'(fields ...)
                                               #'(subfields ...)
                                               rfields
                                               #'(param-fields ...)))
     (with-syntax ([((good real-good) ...) good-sels]
                   [(bad ...) bad-sels]
                   [(debug-params ...)
                    (append (syntax->list
                             (if super-info
                                 (car (cddddr super-info))
                                 #'()))
                            (syntax->list #'(param-fields ...)))]
                   [(rfields ...) rfields])
     #`(begin (struct container super-op ... (subfields ...) #:prefab)
              (define-syntax-parameter param-fields #f) ...
              (define-syntax (name syn)
                (syntax-parse syn
                  [(_ parent-rfields ... rfields ...)
                   #'(container parent-subfields ... subfields ...)]
                  [n:id (raise-syntax-error #f "Not first class" syn)]))
              (define #,name? #,real-name?)
              (define good real-good) ...
              ;; Make sure things compile but I get good error messages
              ;; if I have runtime logic errors.
              (define (bad . rest)
                (error 'bad "Not present in specialized representation")) ...
              (define-match-expander name-ex expander)))]))