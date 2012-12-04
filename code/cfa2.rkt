#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "prealloc.rkt" "imperative.rkt" "fix.rkt" "handle-limits.rkt"
         "data.rkt" "ast.rkt"
         "graph.rkt"
         (for-template "op-struct.rkt" racket/base racket/stxparam)
         (for-syntax racket/syntax))
(provide with-cfa2^ prepare-cfa2^)

;; Instead of heap-allocating continuation frames, pushdown systems
;; handle pushing and popping in a better way. In CFA2, a pushes only happen
;; at non-tail calls, and pops happen at the end of a function call.
;; What is pushed and popped are sections of continuations that are split at
;; function boundaries and annotated with the entry of the function that a return
;; would end up in.

(struct entry (fn #;ρ ξ) #:prefab)
(define L #f) ;; Map[entry, Set[Pair[KontSection, Frame]]] (non-tail-call continuations)
(define M #f) ;; Map[entry, Set[Value]]
(define Ξ? #f)
(define (push! entry pair) (hash-set! L entry (∪1 (hash-ref L entry ∅) pair)))
(define (add-memo! entry v) (hash-set! M entry (∪1 (hash-ref M entry ∅) v)))
(define (add-memos! entry vs) (hash-set! M entry (∪ (hash-ref M entry ∅) vs)))

(define (prepare-cfa2^ parser sexp)
  (set! L (make-hash))
  (set! M (make-hash))
  (set! Ξ? (make-hasheq))
  (define e (prepare-prealloc parser sexp))
  (classify-bindings! e)
  (pretty-print e) (newline)
  (printf "Stack coloring:~%")
  (pretty-print Ξ?)
  e)

(define (classify-bindings! e)
  (let loop ([e e] [ξ (seteq)])
    (match e
      [(var _ _ name) (unless (name . ∈ . ξ)
                        (hash-set! Ξ? name #f))]
      [(lrc _ _ xs es e)
       (define ξ* (∪/l ξ xs))
       (for ([x (in-list xs)]) (hash-set! Ξ? x #t))
       (for ([e (in-list es)]) (loop e ξ*))
       (loop e ξ*)]
      [(lam _ _ vars body)
       (for ([x (in-list vars)]) (hash-set! Ξ? x #t))
       (loop body (list->seteq vars))]
      [(rlm _ _ vars rest body)
       (for ([x (in-list (cons rest vars))]) (hash-set! Ξ? x #t))
       (loop body (∪1 (∪/l ξ vars) rest))]
      [(app _ _ rator rands)
       (for ([rand (in-list rands)]) (loop rand ξ))
       (match rator
         ;; specialize let
         [(lam _ _ vars body)
          (for ([x (in-list vars)]) (hash-set! Ξ? x #t))
          (loop body (∪/l ξ vars))]
         [_ (loop rator ξ)])]
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
      [(or (primr _ _ _)
           (datum _ _ _)
           (fal _ _)) (void)]
      [(or (grt _ _ _ e) (frm _ _ _ e))
       (loop e ξ)]
      [(tst _ _ _ t e)
       (loop t ξ)
       (loop e ξ)])))

(define-for-syntax (apply-transformer f)
  (if (rename-transformer? f)
      (let ([target (rename-transformer-target f)])
        (λ (stx) #`(#,target . #,(cdr (syntax-e stx)))))
      f))

(define-for-syntax ((mk-cfa2 ev co ap mt) stx)
  (syntax-case stx ()
    [(_ (ξ) body ...)
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
           (define-for-syntax (cfa2-yield fnξ)
             (with-syntax ([fn-call-ξ fnξ])
               ;; When constructing a continue state, we might need to pop
               ;; and add a memo table entry.
               ;; Do so when we have to.
               (let ([yield-tr (syntax-parameter-value #'yield)])
                 (λ (stx)
                    (syntax-case stx (co ev)
                      [(_ (co σ k v))
                       #,#'#`(let ([k* k]
                                   [v* v])
                               (cond
                                [(entry? k*)
                                 (add-memo! k* v*)
                                 (define seen (make-hasheq))
                                 (let memo-tail ([konts (hash-ref L k*)])
                                   (for ([kont (in-set konts)]
                                         #:unless (hash-has-key? seen kont))
                                     (hash-set! seen kont #t)
                                     (match-define (cons κ ξ*) kont)
                                     (cond
                                      [(entry? κ)
                                       (add-memo! κ v*)
                                       (memo-tail (hash-ref L κ))]
                                      [else
                                       (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                                         #,(yield-tr #'(yield (co σ κ v*))))])))]
                                [else
                                 #,(yield-tr #'(yield (co σ k* v*)))]))]
                      ;; If this is the product of a function call,
                      ;; push the continuation + stack frame for the entry.
                      [(_ (ev σ e ρ k δ))
                       #,#'#`(let* ([ok k]
                                    [k* (if fn-call-ξ
                                            ;; ξ bound to new stack frame.
                                            (entry e ξ)
                                            ok)])
                               (when fn-call-ξ
                                 (define pair (cons ok fn-call-ξ))                                 
                                 ;; new entry points to old continuation and stack frame.
                                 (push! k* pair)
                                 (define memos (hash-ref M k* ∅))
                                 (unless (∅? memos)
                                   (define seen (make-hasheq))
                                   (let forward ([konts (set pair)])
                                     (for ([kont (in-set konts)]
                                           ;; Could have cycles in call graph.
                                           #:unless (hash-has-key? seen kont))
                                       (hash-set! seen kont #t)
                                       (match-define (cons κ ξ*) kont)
                                       (cond
                                        ;; Tail call: memoize and continue down the call chain.
                                        [(entry? κ)
                                         (add-memos! κ memos) ;; transitive summaries.
                                         (forward (hash-ref L κ))]
                                        ;; Install continuation and the previous stack frame.
                                        [else
                                         (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                                           (for ([v (in-set memos)])
                                             #,(yield-tr #'(yield (co σ κ v)))))])))))
                               ;; Continue to the function/other ev state.
                               #,(yield-tr #'(yield (ev σ e ρ k* δ))))]
                      [(_ e) (yield-tr #'(yield e))])))))

           (define-syntax-rule (bind-extra-initial-cfa2 body* (... ...))
             (let ([ξ₀ (hash)]
                   [fn-call-ξ #f])
               (syntax-parameterize ([ξ (make-rename-transformer #'ξ₀)]
                                     [yield (cfa2-yield #'fn-call-ξ)])
                 body* (... ...))))

           (define-syntax-rule (bind-extra-cfa2 (state ξ*) body* (... ...))
             (let ([fn-call-ξ (and (ap? state) ξ*)])
               (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)]
                                     [yield (cfa2-yield #'fn-call-ξ)])
                 body* (... ...))))

           (define-simple-macro* (bind-join-cfa2 (σ* σ a vs) body*)
             (let-values ([(ξ* vs*)
                           (cond [(hash-ref Ξ? a #f)
                                  (values (hash-set ξ a vs) nothing)]
                                 [else (values ξ vs)])])
               (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                 #,((apply-transformer bind-join-tr)
                    #'(bind-join (σ* σ a vs*) body*)))))

           (define-simple-macro* (bind-join*-cfa2 (σ* σ as vss) body*)
             (let*-values ([(vss*) vss]
                           [(ξ* rvss*)
                            (for/fold ([ξ* ξ] [rvss* '()]) 
                                ([a (in-list as)]
                                 [vs (in-list vss*)])
                              (cond [(hash-ref Ξ? a #f)
                                     (values (hash-set ξ* a vs) (cons nothing rvss*))]
                                    [else (values ξ* (cons vs rvss*))]))]
                           [(vss*) (reverse rvss*)])
               (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                 #,((apply-transformer bind-join*-tr)
                    #'(bind-join* (σ* σ as vss*) body*)))))

           (define-syntax-rule (bind-get-kont-cfa2 (res σ k) body*)
             ;; Use let-syntax so that for's singleton optimization kicks in.
             (let-syntax ([res (λ (stx) (syntax-case stx () [_ #'(singleton k)]))]) body*))

           (define-syntax-rule (bind-push-cfa2 (σ* a* σ l δ k) body*)
             (let ([a* k]) body*))

           (define-simple-macro* (mk-getter name ξ*)
             (define-syntax-rule (name σ a)
               (or (hash-ref ξ* a #f)
                   #,((apply-transformer getter-tr) #'(getter σ a)))))
           (mk-getter getter-cfa2 ξ)

           ;; Make a new stack frame before entering a new function
           (define-simple-macro* (bind-rest-cfa2 (ρ* σ* δ*) (ρ iσ l δ xs r v-addrs) body*)
             (let ([oldξ ξ]
                   [newξ (hash)])
               (mk-getter bind-rest-getter oldξ)
               (syntax-parameterize ([ξ (make-rename-transformer #'newξ)]
                                     [getter (make-rename-transformer #'bind-rest-getter)])
                 #,((apply-transformer bind-rest-tr)
                    #'(bind-rest (ρ* σ* δ*) (ρ iσ i δ xs r v-addrs)
                        (syntax-parameterize ([getter (make-rename-transformer #'getter-cfa2)])
                          body*))))))

           ;; Likewise
           (define-simple-macro* (bind-cfa2 (ρ* σ* δ*) (ρ bσ l δ xs v-addrs) body*)
             (let ([oldξ ξ]
                   [newξ (hash)])
               (mk-getter bind-getter oldξ)
               (syntax-parameterize ([ξ (make-rename-transformer #'newξ)]
                                     [getter (make-rename-transformer #'bind-getter)])
                 #,((apply-transformer bind-tr)
                    #'(bind (ρ* σ* δ*) (ρ bσ i δ xs v-addrs)
                        (syntax-parameterize ([getter (make-rename-transformer #'getter-cfa2)])
                          body*))))))

           ;; No heap change since guaranteed local. No previous value because
           ;; only one join point.
           (define-simple-macro* (bind-join-local-cfa2 (σ* σ a vs) body*)
             ;;#,((apply-transformer bind-join-tr) #'(bind-join (σ* σ a vs) body*))             
             (let ([ξ* (hash-set ξ a vs)])
               (syntax-parameterize ([ξ (make-rename-transformer #'ξ*)])
                 body*)))
           (splicing-syntax-parameterize
               ([bind-join (make-rename-transformer #'bind-join-cfa2)]
                [bind-join-local (make-rename-transformer #'bind-join-local-cfa2)]
                [bind-join* (make-rename-transformer #'bind-join*-cfa2)]
                [getter (make-rename-transformer #'getter-cfa2)]
                [bind-get-kont (make-rename-transformer #'bind-get-kont-cfa2)]
                [bind-push (make-rename-transformer #'bind-push-cfa2)]
                [bind-extra (make-rename-transformer #'bind-extra-cfa2)]
                [bind-extra-initial (make-rename-transformer #'bind-extra-initial-cfa2)]
                [bind (make-rename-transformer #'bind-cfa2)]
                [bind-rest (make-rename-transformer #'bind-rest-cfa2)]
                [ξ (λ (stx) (raise-syntax-error #f "Whoa" stx))])
             body ...)
           (void)))]))

(define-syntax-rule (with-cfa2^ (mk-analysis) body)
  (splicing-let-syntax ([mk-analysis
                         (syntax-rules ()
                           [(_ . args)
                            (splicing-syntax-parameterize ([in-scope-of-extras (mk-cfa2 #'ev #'co #'ap #'mt)])
                              (mk-analysis #:extra (ξ)
                                           #:ev ev
                                           #:co co
                                           #:ap ap
                                           #:mt mt
                                           . args))])])
                       body))