#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "prealloc.rkt" "imperative.rkt" "fix.rkt" "handle-limits.rkt"
         "data.rkt" "ast.rkt"
         "graph.rkt"
         (for-template "op-struct.rkt" racket/base racket/stxparam)
         (for-syntax racket/syntax))
(provide with-pdcfa^ prepare-pdcfa^)

(struct entry (fn #;ρ) #:prefab)
(define L #f) ;; Map[entry, Set[Pair[KontSection, Frame]]] (non-tail-call continuations)
(define M #f) ;; Map[entry, Set[Value]]
(define (push! entry k) (hash-set! L entry (∪1 (hash-ref L entry ∅) k)))
(define (add-memo! entry v) (hash-set! M entry (∪1 (hash-ref M entry ∅) v)))
(define (add-memos! entry vs) (hash-set! M entry (∪ (hash-ref M entry ∅) vs)))

(define (prepare-pdcfa^ parser sexp)
  (set! L (make-hash))
  (set! M (make-hash))
  (prepare-prealloc parser sexp))

(define-for-syntax (apply-transformer f)
  (if (rename-transformer? f)
      (let ([target (rename-transformer-target f)])
        (λ (stx) #`(#,target . #,(cdr (syntax-e stx)))))
      f))

(define-for-syntax ((mk-pdcfa ev co ap mt) stx)
  (syntax-case stx ()
    [(_ () body ...)
     (with-syntax ([co co]
                   [ev ev]
                   [mt? (format-id mt "~a?" mt)]
                   [ap? (format-id ap "~a?" ap)])
       (define getter-tr (syntax-parameter-value #'getter))
       (define bind-join-tr (syntax-parameter-value #'bind-join))
       (define bind-join*-tr (syntax-parameter-value #'bind-join*))
       (define bind-tr (syntax-parameter-value #'bind))
       (define bind-rest-tr (syntax-parameter-value #'bind-rest))
       #`(splicing-let ()
           (define-for-syntax (pdcfa-yield fnc?)
             (with-syntax ([fn-call? fnc?])
             ;; When constructing a continue state, we might need to pop
               ;; and add a memo table entry.
               ;; Do so when we have to.
               (let ([yield-tr (syntax-parameter-value #'yield)])
                 (λ (stx)
                    (syntax-case stx (co ev)
                      [(_ (co σ k v))
                       #,#'#`(let ([k* k]
                                   [v* v*])
                               (cond
                                [(entry? k*)
                                 (add-memo! k* v*)
                                 (define seen (make-hasheq))
                                 (let memo-tail ([konts (hash-ref L k*)])
                                   (for ([kont (in-set konts)]
                                         #:unless (hash-has-key? seen kont))
                                     (hash-set! seen kont #t)
                                     (cond
                                      [(entry? kont)
                                       (add-memo! kont v*)
                                       (memo-tail (hash-ref L kont))]
                                      [else #,(yield-tr #'(yield (co σ kont v*)))])))]
                                [else
                                 #,(yield-tr #'(yield (co σ k* v*)))]))]
                      ;; If this is the product of a function call,
                      ;; push the continuation + stack frame for the entry.
                      [(_ (ev σ e ρ k δ))
                       #,#'#`(let* ([ok k]
                                    [k* (if fn-call?
                                            (entry e)
                                            ok)])
                               (when fn-call?
                                 (push! k* ok)
                                 (define memos (hash-ref M k* ∅))
                                 (unless (∅? memos)
                                   (define seen (make-hasheq))
                                   (let forward ([konts (set ok)])
                                     (for ([kont (in-set konts)]
                                           #:unless (hash-has-key? seen kont))
                                       (hash-set! seen kont #t)
                                       (cond
                                        [(entry? kont)
                                         (add-memos! kont memos) ;; transitive summaries.
                                         (forward (hash-ref L kont))]
                                        [else
                                         (for ([v (in-set memos)])
                                           #,(yield-tr #'(yield (co σ kont v))))])))))
                               #,(yield-tr #'(yield (ev σ e ρ k* δ))))]
                      [(_ e) (yield-tr #'(yield e))])))))

           (define-syntax-rule (bind-extra-initial-pdcfa body* (... ...))
             (let ([fn-call? #f])
               (syntax-parameterize ([yield (pdcfa-yield #'fn-call?)])
                 body* (... ...))))

           (define-syntax-rule (bind-extra-pdcfa (state) body* (... ...))
             (let ([fn-call? (ap? state)])
               (syntax-parameterize ([yield (pdcfa-yield #'fn-call?)])
                 body* (... ...))))

           (define-syntax-rule (bind-get-kont-pdcfa (res σ k) body*)
             ;; Use let-syntax so that for's singleton optimization kicks in.
             (let-syntax ([res (λ (stx) (syntax-case stx () [_ #'(singleton k)]))]) body*))

           (define-syntax-rule (bind-push-pdcfa (σ* a* σ l δ k) body*)
             (let ([a* k]) body*))

           (splicing-syntax-parameterize
               ([bind-get-kont (make-rename-transformer #'bind-get-kont-pdcfa)]
                [bind-push (make-rename-transformer #'bind-push-pdcfa)]
                [bind-extra (make-rename-transformer #'bind-extra-pdcfa)]
                [bind-extra-initial (make-rename-transformer #'bind-extra-initial-pdcfa)])
             body ...)
           (void)))]))

(define-syntax-rule (with-pdcfa^ (mk-analysis) body)
  (splicing-let-syntax ([mk-analysis
                         (syntax-rules ()
                           [(_ . args)
                            (splicing-syntax-parameterize ([in-scope-of-extras (mk-pdcfa #'ev #'co #'ap #'mt)])
                              (mk-analysis #:ev ev
                                           #:co co
                                           #:ap ap
                                           #:mt mt
                                           . args))])])
                       body))