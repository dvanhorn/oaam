#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "prealloc.rkt" "imperative.rkt" "fix.rkt" "handle-limits.rkt"
         "data.rkt" "ast.rkt" "parameters.rkt"
         "graph.rkt"
         racket/unsafe/ops
         racket/trace
         (for-template "op-struct.rkt" racket/base racket/stxparam)
         (for-syntax racket/syntax))
(provide with-cfa2^ with-prepare-cfa2^)

;; Instead of heap-allocating continuation frames, pushdown systems
;; handle pushing and popping in a better way. In CFA2, a pushes only happen
;; at non-tail calls, and pops happen at the end of a function call.
;; What is pushed and popped are sections of continuations that are split at
;; function boundaries and annotated with the entry of the function that a return
;; would end up in.

(struct entry (ξ fnv) #:prefab)
(define L #f) ;; Map[entry, Set[HeterogeneousList[KontSection, Frame, Addr]]]
(define M #f) ;; Map[entry, Set[Value]]
(define Ξ? #f)
(define fake-rebinding-candidates #f)
(define (push! entry pair) (hash-set! L entry (∪1 (hash-ref L entry ∅) pair)))
(define (add-memo! entry v) (hash-set! M entry (∪1 (hash-ref M entry ∅) v)))
(define (add-memos! entry vs) (hash-set! M entry (∪ (hash-ref M entry ∅) vs)))

;; Global σ
(define (do-co-yield ξ #;σ k v do)
  (match k
   [(entry _ fnv)
    (define v* (match v ;; don't let stack addresses escape. Resolve them at return.
                 [(addr a) (if (hash-ref Ξ? a #f)
                               (value-set (hash-ref ξ a))
                               v)]
                 [_ v]))
    (add-memo! k v*)
    ;; XXX: Is this fresh seen hash adding more states than necessary?
    (define seen (make-hasheq))
    (let memo-tail ([konts (hash-ref L k)] [last fnv])
      (for ([kont (in-set konts)]
            #:unless (hash-has-key? seen kont))
        (hash-set! seen kont #t)
        (match kont
          [(list κ ξ* maybe-addr)
           ;; Fake-rebinding
           (define ξ** (if maybe-addr
                           (hash-set ξ* maybe-addr last)
                           ξ*))
           (do ξ** κ v*)]
          [(entry _ fnv)
           (add-memo! kont v*)
           (memo-tail (hash-ref L kont) fnv)])))]
   [_ (do ξ k v)]))

(define (call-prep fn-call-ξ fn-call-label ok ent do #;original-δ)
  ;; new entry points to old continuation and stack frame.
  (define prev (if (entry? ok)
                   ok
                   (list ok fn-call-ξ
                         ;; Monovariant
                         (hash-ref fake-rebinding-candidates
                                   fn-call-label #f)
                         ;; Polyvariant
                         #;
                         (make-var-contour (hash-ref fake-rebinding-candidates
                                                     fn-call-label #f)
                                           original-δ))))
  (push! ent prev)
  (define memos (hash-ref M ent ∅))
  (unless (∅? memos)
    (define seen (make-hasheq))
    (let forward ([konts (set prev)] [last (entry-fnv ent)])
      (for ([kont (in-set konts)]
            ;; Could have cycles in call graph.
            #:unless (hash-has-key? seen kont))
        (hash-set! seen kont #t)
        (match kont
          ;; Install continuation and the previous stack frame.
          [(list κ ξ* maybe-addr)
           ;; Fake-rebinding
           (define ξ** (if maybe-addr
                           (hash-set ξ* maybe-addr last)
                           ξ*))
           (for ([v (in-set memos)]) (do ξ** κ v))]
          ;; Tail call: memoize and continue down the call chain.
          [(entry _ fnv)
           (add-memos! kont memos) ;; transitive summaries.
           (forward (hash-ref L kont) fnv)])))))

#;(trace bind-Ξ bind-Ξ*)

(define-syntax-rule (with-prepare-cfa2^ (name) . rest)
  (begin
    (with-prepare-prealloc (prepare-prealloc)
      (define (name parser sexp)
        (set! L (make-hash))
        (set! M (make-hash))
        (set! Ξ? (make-hasheq))
        (set! fake-rebinding-candidates (make-hasheq))
        (define e (prepare-prealloc parser sexp))
        (classify-bindings! e)
        (pretty-print e) (newline)
        (printf "Stack coloring:~%")
        (pretty-print Ξ?)
        e))
    . rest))

(define (classify-bindings! e)
  (define check-classification (make-hasheq))
  (let loop ([e e] [ξ (seteq)])
    (define (add-fresh xs)
      (for/fold ([ξ ξ]) ([x (in-list xs)])
        (hash-set! Ξ? x #t)
        (∪1 ξ x)))
    (match e
      [(var _ _ name) (unless (name . ∈ . ξ)
                        (hash-set! Ξ? name #f))]
      [(lrc _ _ xs es e)
       (define ξ* (add-fresh xs))
       (for ([e (in-list es)]) (loop e ξ*))
       (loop e ξ*)]
      [(lam _ _ vars body)
       (for ([x (in-list vars)]) (hash-set! Ξ? x #t))
       (loop body (list->seteq vars))]
      [(rlm _ _ vars rest body)
       (hash-set! Ξ? rest #f) ;; self-references.
       (for ([x (in-list vars)]) (hash-set! Ξ? x #t))
       (loop body (∪1 (∪/l ξ vars) rest))]
      [(app l _ rator rands)
       (match rator
         [(var _ _ name) (when (name . ∈ . ξ)
                           (hash-set! check-classification l name))]
         [_ (void)])
       (for ([rand (in-list rands)]) (loop rand ξ))
       (loop rator ξ)]
      [(lte _ _ xs es e)
       (define ξ* (add-fresh xs))
       (for ([e (in-list es)]) (loop e ξ))
       (loop e ξ*)]
      [(ife _ _ g t e)
       (loop g ξ)
       (loop t ξ)
       (loop e ξ)]
      [(st! _ _ x e)
       (unless (x . ∈ . ξ)
         (hash-set! Ξ? x #f))
       (loop e ξ)]
      [(lcc _ _ x e)
       (loop e (∪1 ξ x))]
      [(pfl _ _ _ e) (loop e ξ)]
      [(or (primr _ _ _ _)
           (datum _ _ _)
           (fal _ _)) (void)]
      [(or (grt _ _ _ e) (frm _ _ _ e))
       (loop e ξ)]
      [(tst _ _ _ t e)
       (loop t ξ)
       (loop e ξ)]))
  ;; With all stack references classified, classify
  ;; which variables can have their values narrowed upon
  ;; return
  (for ([(label name) (in-hash check-classification)]
        #:when (hash-ref Ξ? name #f))
    (hash-set! fake-rebinding-candidates label name)))

(define-syntax-parameter fn-call-ξ #f)
(define-syntax-parameter fn-call-label #f)
(begin-for-syntax
 (define fnξ-target (target #'fn-call-ξ '#:fnξ (syntax-rules () [(_ e) e])))
 (define fnlab-target (target #'fn-call-label '#:fnlab (syntax-rules () [(_ e) e])))
 (define ((mk-cfa2 ev co ap) stx)
   (syntax-case stx ()
     [(_ (ξ) body ...)
      (with-syntax ([co co]
                    [ev ev]
                    [ap: (format-id ap "~a:" ap)])
        (define getter-tr (syntax-parameter-value #'getter))
        (define bind-join-tr (syntax-parameter-value #'bind-join))
        (define bind-tr (syntax-parameter-value #'bind))
        (define bind-rest-tr (syntax-parameter-value #'bind-rest))
        (define bind-rest-apply-tr (syntax-parameter-value #'bind-rest-apply))
        #`(splicing-let ()
            (define-for-syntax cfa2-yield
              ;; When constructing a continue state, we might need to pop
              ;; and add a memo table entry.
              ;; Do so when we have to.
              (let ([yield-tr (syntax-parameter-value #'yield)])
                (λ (stx)
                   (syntax-case stx (co ev)
                     [(_ (co σ k v))
                      #,#'#`(let* ([k* k]
                                   [v* v]
                                   [do (λ (ξ** k** v**)
                                          (syntax-parameterize ([ξ (make-rename-transformer #'ξ**)])
                                            #,(yield-tr #'(yield (co σ k** v**)))))])
                              (do-co-yield ξ k* v* do)
                              (values))]
                     ;; If this is the product of a function call,
                     ;; push the continuation + stack frame for the entry.
                     [(_ (ev σ e ρ k δ*))
                      (let ()
                        (define do-co                        
                          #,#'#`(λ (ξ* k* v*)
                                   (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                                     #,(yield-tr #'(yield (co σ k* v*))))))
                        (define (do-ev k-stx)
                          (yield-tr #,#'#`(yield (ev σ e ρ #,k-stx δ*))))
                        #,#'#`(let* ([ok k]
                                     [k*
                                      (if called-function
                                          (let ([k* (entry ξ (singleton called-function))])
                                            (call-prep fn-call-ξ fn-call-label ok k* #,do-co #;original-δ)
                                            k*)
                                          ok)])
                                #,(do-ev #'k*)))]
                      [(_ e) (yield-tr #'(yield e))]))))

              (define-syntax-rule (bind-extra-initial-cfa2 . body*)
                (let ([ξ₀ (hash)]
                      [fnξ (hash)]
                      [fnlab -1])
                  (syntax-parameterize ([ξ (make-rename-transformer #'ξ₀)]
                                        [fn-call-ξ (make-rename-transformer #'fnξ)]
                                        [fn-call-label (make-rename-transformer #'fnlab)])
                    . body*)))

              (define-syntax-rule (bind-extra-cfa2 (state ξ*) . body*)
                (let-values ([(fnξ fnlab)
                              (match state
                                [(ap: _ ξ* l _ _ _ _) (values ξ* l)]
                                [_ (values #f #f)])])
                  (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)]
                                        [fn-call-ξ (make-rename-transformer #'fnξ)]
                                        [fn-call-label (make-rename-transformer #'fnlab)])
                    . body*)))

              (define-syntax-rule (bind-extra-prim-cfa2 (state ℓ ξ*) . body*)
                (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)]
                                      [fn-call-ξ (make-rename-transformer #'ξ*)]
                                      [fn-call-label (make-rename-transformer #'ℓ)])
                  . body*))

              (define (bind-Ξ ξ a vs)
                (cond [(hash-ref Ξ? a #f)
                       (values (hash-set ξ a vs) nothing)]
                      [else (values ξ vs)]))

              (define (bind-Ξ* ξ as vss)
                (define-values (ξ* rvss)
                  (for/fold ([ξ* ξ] [rvss '()])
                      ([a (in-list as)]
                       [vs (in-list vss)])
                    (cond [(hash-ref Ξ? a #f)
                           (values (hash-set ξ* a vs) (cons nothing rvss))]
                          [else (values ξ* (cons vs rvss))])))
                (values ξ* (alt-reverse rvss)))

              (define-simple-macro* (bind-join-cfa2 (σ* σ a vs) body*)
                (let*-values ([(-a) a]
                              [(-vs) vs]
                              [(ξ* vs*) (bind-Ξ ξ -a -vs)])
                  (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                    #,(apply-transformer bind-join-tr #'(bind-join (σ* σ -a vs*) body*)))))

              (define-syntax-rule (bind-get-kont-cfa2 (res σ k) body*)
                ;; Use let-syntax so that for's singleton optimization kicks in.
                (let-syntax ([res (λ (stx) (syntax-case stx () [_ #'(singleton k)]))]) body*))

              (define-syntax-rule (bind-push-cfa2 (σ* a* σ l δ k) body*)
                (let ([a* k]) body*))

              (define-simple-macro* (mk-getter name ξ*)
                (define-syntax-rule (name σ a)
                  #;
                  (or (hash-ref ξ* a #f) #,(apply-transformer getter-tr #'(getter σ a)))

                  (let ([s (hash-ref ξ* a #f)])
                    (cond [s (when (∅? s) (error 'name "bad stack ~a" a))
                             s]
                          [else (define res #,(apply-transformer getter-tr #'(getter σ a)))
                                (when (∅? res) (error 'name "bad store ~a" a))
                                res]))))
              (mk-getter getter-cfa2 ξ)

              ;; Make a new stack frame before entering a new function
              (define-simple-macro* (bind-rest-cfa2 (ρ* σ* δ*) (ρ iσ l δ xs r v-addrs) body*)
                (let ([oldξ ξ]
                      [newξ (hash)])
                  (mk-getter bind-rest-getter oldξ)
                  (syntax-parameterize ([ξ (make-rename-transformer #'newξ)]
                                        [getter (make-rename-transformer #'bind-rest-getter)])
                    #,(apply-transformer bind-rest-tr
                                         #'(bind-rest (ρ* σ* δ*) (ρ iσ i δ xs r v-addrs)
                                                      (syntax-parameterize ([getter (make-rename-transformer #'getter-cfa2)])
                                                        body*))))))
              (define-simple-macro* (bind-rest-apply-cfa2 (ρ* σ* δ*) (ρ iσ l δ xs r v-addrs) body*)
                (let ([oldξ ξ]
                      [newξ (hash)])
                  (mk-getter bind-rest-getter oldξ)
                  (syntax-parameterize ([ξ (make-rename-transformer #'newξ)]
                                        [getter (make-rename-transformer #'bind-rest-getter)])
                    #,(apply-transformer
                       bind-rest-apply-tr
                       #'(bind-rest-apply (ρ* σ* δ*) (ρ iσ i δ xs r v-addrs)
                                          (syntax-parameterize ([getter (make-rename-transformer #'getter-cfa2)])
                                            body*))))))
              ;; Likewise
              (define-simple-macro* (bind-cfa2 (ρ* σ* δ*) (ρ bσ l δ xs v-addrs) body*)
                (let ([oldξ ξ]
                      [newξ (hash)])
                  (mk-getter bind-getter oldξ)
                  (syntax-parameterize ([ξ (make-rename-transformer #'newξ)]
                                        [getter (make-rename-transformer #'bind-getter)])
                    #,(apply-transformer
                       bind-tr
                       #'(bind (ρ* σ* δ*) (ρ bσ i δ xs v-addrs)
                               (syntax-parameterize ([getter (make-rename-transformer #'getter-cfa2)])
                                 body*))))))

              ;; No heap change since guaranteed local. No previous value because
              ;; only one join point.
              (define-simple-macro* (bind-join-local-cfa2 (σ* σ a vs) body*)
                ;;#,(apply-transformer bind-join-tr #'(bind-join (σ* σ a vs) body*))
                (let ([ξ* (hash-set ξ a vs)])
                  (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                    body*)))

              (define-for-syntax ξ-target (target #'ξ '#:ξ (syntax-rules () [(_ e) e])))
              (splicing-syntax-parameterize
                  ([al-targets (cons ξ-target (syntax-parameter-value #'al-targets))]
                   [av-targets (list* fnξ-target fnlab-target called-fn-target
                                      (syntax-parameter-value #'av-targets))]
                   [bind-get-kont (make-rename-transformer #'bind-get-kont-cfa2)]
                   [bind-push (make-rename-transformer #'bind-push-cfa2)]
                   [bind-extra (make-rename-transformer #'bind-extra-cfa2)]
                   [bind-extra-initial (make-rename-transformer #'bind-extra-initial-cfa2)]
                   [bind-extra-prim (make-rename-transformer #'bind-extra-prim-cfa2)]
                   [yield cfa2-yield]
                   [prim-extras (list #'fn-call-ξ #'fn-call-label)]
                   ;; Extra parameters over pdcfa for stack allocation.
                   [bind-join (make-rename-transformer #'bind-join-cfa2)]
                   [bind-join-local (make-rename-transformer #'bind-join-local-cfa2)]
                   [getter (make-rename-transformer #'getter-cfa2)]
                   [bind (make-rename-transformer #'bind-cfa2)]
                   [bind-rest (make-rename-transformer #'bind-rest-cfa2)]
                   [bind-rest-apply (make-rename-transformer #'bind-rest-apply-cfa2)]
                   [ξ (λ (stx) (raise-syntax-error #f "Whoa" stx))])
                body ...)))])))

(define-syntax-rule (with-cfa2^ (mk-analysis) body)
  (splicing-let-syntax ([mk-analysis
                         (syntax-rules ()
                           [(_ . args)
                            (splicing-syntax-parameterize ([in-scope-of-extras (mk-cfa2 #'ev #'co #'ap)])
                              (mk-analysis #:extra (ξ)
                                           #:ev ev
                                           #:co co
                                           #:ap ap
                                           . args))])])
                       body))