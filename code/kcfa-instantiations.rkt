#lang racket
(require (rename-in racket/generator [yield real-yield]))
(require "kcfa.rkt" "data.rkt" "parse.rkt" "notation.rkt"
         "primitives.rkt" "fix.rkt" "env.rkt"
         (for-syntax syntax/parse
                     syntax/srcloc)
         racket/stxparam
         racket/splicing)

;; Utility function for combining multiple σ-∆s
(define (map2-append f acc ls0 ls1)
  (let loop ([ls0 ls0] [ls1 ls1])
    (match* (ls0 ls1)
      [((cons h0 t0) (cons h1 t1))
       (cons (f h0 h1) (loop t0 t1))]
      [('() '()) acc]
      [(_ _)
       (error 'map2-append "Expected same length lists. Finished at ~a ~a"
              ls0 ls1)])))

(define-for-syntax (bind-rest inner-σ body)
  #`(syntax-parameterize ([target-σ (make-rename-transformer #'#,inner-σ)])
      #,body))
(define-simple-macro* (bind-join-whole (σjoin σ a vs) body)
  (let ([σjoin (join σ a vs)]) #,(bind-rest #'σjoin #'body)))
(define-simple-macro* (bind-join*-whole (σjoin* σ as vss) body)
  (let ([σjoin* (join* σ as vss)]) #,(bind-rest #'σjoin* #'body)))
(define-simple-macro* (bind-join-∆s (∆s* ∆s a vs) body)
  (let ([∆s* (cons (cons a vs) ∆s)]) #,(bind-rest #'∆s* #'body)))
(define-simple-macro* (bind-join*-∆s (∆s* ∆s as vss) body)
  (let ([∆s* (map2-append cons ∆s as vss)]) #,(bind-rest #'∆s* #'body)))

(define-for-syntax ((mk-bind σ-∆s? K) stx)
  (syntax-parse stx
    [(_ (ρ* σ* δ*) (ρ σ l δ xs v-addrs) body)
     (define vs
       (quasisyntax/loc stx
         (map (λ (v) (getter #,(if σ-∆s? #'top-σ #'σ) v)) v-addrs)))
     (if (zero? K)
         (quasisyntax/loc stx
           (bind-join* (σ* σ xs #,vs) body))
         (quasisyntax/loc stx
           (let* ([δ* (truncate (cons l δ) #,K)]
                  [as (map (λ (x) (cons x δ*)) xs)]
                  [ρ* (extend* ρ xs as)])
             (bind-join* (σ* σ as #,vs) body))))]))
(define-syntax-rule (make-var-contour-0 x δ) x)
(define-syntax-rule (make-var-contour-k x δ) (cons x δ))

(define-syntax bind-0 (mk-bind #f 0))
(define-syntax bind-∞ (mk-bind #f +inf.0))
(define-syntax bind-∆s-0 (mk-bind #t 0))
(define-syntax bind-∆s-∞ (mk-bind #t +inf.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widen set-monad fixpoint
(define-syntax-rule (wide-step step)
  (λ (state)
     (match state
       [(cons σ cs)
        (define-values (σ* cs*)
          (for/fold ([σ* σ] [cs ∅]) ([c (in-set cs)])
            (define-values (σ** cs*) (step (cons σ c)))
            (values (join-store σ* σ**) (∪ cs* cs))))
        (set (cons σ* cs*))]
       [_ (error 'wide-step "bad output ~a~%" state)])))

(define-syntax-rule (mk-set-fixpoint^ fix name ans^?)
 (define-syntax-rule (name step fst)
   (let-values ([(σ cs) fst])
     (for/fold ([last-σ (hash)]
                [final-cs ∅])
         ([s (fix (wide-step step) (set (cons σ cs)))])
       (match s
         [(cons σ cs)
          (define-values (σ* cs*)
            (values (join-store last-σ σ)
                    (for/set #:initial final-cs ([c (in-set cs)]
                                                 #:when (ans^? c))
                             c)))
          (values σ* cs*)]
         [_ (printf "bad output ~a~%" s)])))))

(define-syntax-rule (pull gen ∆-base cs-base)
  (let*-values ([(cs ∆)
                 (for/fold ([cs cs-base] [last #f])
                     ([c (in-producer gen (λ (x) (eq? 'done x)))])
                   (cond [(list? c) (values cs (if last (append c last) c))]
                         [else (values (set-add cs c) last)]))]
                [(∆*) (if (list? ∆) (append ∆ ∆-base) ∆-base)])
    (values cs ∆*)))

(define-syntax-rule (σ-∆s/generator/wide-step-specialized step ans?)
  (λ (state)
     (match state
       [(cons σ cs)
        (define-values (cs* ∆)
          (for/fold ([cs* ∅] [∆* '()])
              ([c cs] #:unless (ans? c))
            (pull (step (cons σ c)) ∆* cs*)))
        (cons (update ∆ σ) (set-union cs cs*))])))

(define-syntax-rule (mk-generator/wide/σ-∆s-fixpoint name ans?)
  (define-syntax-rule (name step fst)
    (let ()
      (define wide-step (σ-∆s/generator/wide-step-specialized step ans?))
      (define-values (cs ∆) (pull fst '() ∅))
      (define fst-s (cons (update ∆ (hash)) cs))
      (define snd (wide-step fst-s))
      (let loop ((next snd) (prev fst-s))
        (cond [(equal? next prev)
               (for/set ([c (cdr prev)]
                         #:when (ans? c))
                 c)]
              [else (loop (wide-step next) next)])))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Wide fixpoint for σ-∆s

(define-syntax-rule (mk-∆-fix^ name ans^?)
  (define-syntax-rule (name stepper fst)
    (let-values ([(∆ cs) fst])
     (define seen (make-hash))
     (define todo (set (cons (update ∆ (hash)) cs)))
     (let loop ()
       (cond [(∅? todo) (for/set ([(c σ) (in-hash seen)]
                                  #:when (ans^? c))
                          (cons σ c))]
             [else (define old-todo todo)
                   (set! todo ∅)
                   (for* ([σ×cs (in-set old-todo)]
                          [σ (in-value (car σ×cs))]
                          [c (in-set (cdr σ×cs))]
                          [last-σ (in-value (hash-ref seen c (hash)))]
                          #:unless (equal? last-σ σ))
                     ;; This state's store monotonically increases
                     (hash-set! seen c (join-store σ last-σ))
                     ;; Add the updated store with next steps to workset
                     (printf "Stepping ~a~%" c)
                     (define-values (∆ cs*) (stepper (cons σ c)))
                     (set! todo (∪1 todo (cons (update ∆ σ) cs*))))
                   (loop)])))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutable pre-allocated store / mutable worklist
(define global-σ #f)
(define todo #f)
(define unions 0)
(define seen #f)
(define next-loc #f)
(define contour-table #f)

(define (ensure-σ-size)
  (when (= next-loc (vector-length global-σ))
    (set! global-σ
          (for/vector #:length (* 2 next-loc) #:fill ∅ ;; ∅ → '()
                      ([v (in-vector global-σ)]
                       [i (in-naturals)]
                       #:when (< i next-loc))
                      v))))

(define-syntax-rule (get-contour-index!-0 c)
  (or (hash-ref contour-table c #f)
      (begin0 next-loc
              (ensure-σ-size)
              (hash-set! contour-table c next-loc)
              (set! next-loc (add1 next-loc)))))

(define-for-syntax yield!
  (syntax-parser [(_ e) #'(let ([c e])
                            (unless (= unions (hash-ref seen c -1))
                              (hash-set! seen c unions)
                              (set! todo (∪1 todo c))))])) ;; ∪1 → cons

(define-syntax-rule (make-var-contour-0-prealloc x δ)
  (cond [(exact-nonnegative-integer? x) x]
        [else (get-contour-index!-0 x)]))

(define (prepare-prealloc parser sexp)
  (define nlabels 0)
  (define (fresh-label!) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define (fresh-variable! x) (begin0 nlabels (set! nlabels (add1 nlabels))))
  (define e (parser sexp fresh-label! fresh-variable!))
  ;; Start with a constant factor larger store since we are likely to
  ;; allocate some composite data. This way we don't incur a reallocation
  ;; right up front.
  (set! global-σ (make-vector (* 2 nlabels) ∅)) ;; ∅ → '()
  (set! next-loc nlabels)
  (set! contour-table (make-hash))
  (set! unions 0)
  (set! todo ∅)
  (set! seen (make-hash))
  e)

(define (join! a vs)
  (define prev (vector-ref global-σ a))
  (define added? (not (subset? vs prev)))
  (when added?
    (vector-set! global-σ a (∪ vs prev))
    (set! unions (add1 unions))))

(define (join*! as vss)
  (for ([a (in-list as)]
        [vs (in-list vss)])
    (join! a vs)))

(define-syntax-rule (bind-join! (σ* σ a vs) body)
  (begin (join! a vs) body))
(define-syntax-rule (bind-join*! (σ* σ as vss) body)
  (begin (join*! as vss) body))

(define-syntax-rule (global-vector-getter σ* a)
  (vector-ref global-σ a))

(define-syntax-rule (mk-prealloc^-fixpoint name ans^? ans^-v 0cfa?)
  (define (name step fst)
    (define clean-σ (if 0cfa?
                        restrict-to-reachable/vector-0
                        restrict-to-reachable/vector-k))
    (let loop ()
      (cond [(∅? todo) ;; → null?
             (define vs
               (for*/set ([(c at-unions) (in-hash seen)]
                          #:when (ans^? c))
                 (ans^-v c)))
             (cons (clean-σ global-σ vs)
                   vs)]
            [else
             (define todo-old todo)
             (set! todo ∅)                        ;; → '()
             (for ([c (in-set todo-old)]) (step c)) ;; → in-list
             (loop)]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete semantics

(define (eval-widen b)
  (cond [(atomic? b) b]
        [else (error "Unknown base value" b)]))

(define (hash-getter σ a)
  (hash-ref σ a (λ () (error 'getter "Unbound address ~a in store ~a" a σ))))

(define-syntax-rule (top-hash-getter σ a)
  (hash-ref top-σ a (λ () (error 'top-hash-getter "Unbound address ~a in store ~a" a σ))))

(define (lazy-force σ x)
  (match x
    [(addr a) (hash-getter σ a)]
    [v (set v)]))

(define-syntax-rule (lazy-force-σ-∆s σ x)
  (match x
    [(addr a)
     (hash-ref top-σ a (λ () (error 'getter "(force) Unbound address ~a in store ~a" a σ)))]
    [v (set v)]))

(define-syntax-rule (lazy-force! σ x)
  (match x
    [(addr a) (vector-ref global-σ a)]
    [v (set v)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define ε '())
(define (truncate δ k)
  (cond [(zero? k) '()]
        [(empty? δ) '()]
        [else
         (cons (first δ) (truncate (rest δ) (sub1 k)))]))

(define (widen^ b)
  (match b
    [(? number?) 'number]
    [(? string?) 'string]
    [(? symbol?) 'symbol]
    [(? boolean?) b]
    [(or 'number 'string 'symbol) b]
    [else (error "Unknown base value" b)]))

(define-syntax-rule (lazy-delay σ a) (set (addr a)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of common parameterizations

(define-syntax-rule (with-concrete body)
  (splicing-syntax-parameterize
   ([widen (make-rename-transformer #'eval-widen)])
   body))

(define-syntax-rule (with-abstract body)
  (splicing-syntax-parameterize
   ([widen (make-rename-transformer #'widen^)])
   body))

(define-syntax-rule (with-narrow-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (∪1 target-cs e)])])
   body))

(define-syntax-rule (with-σ-passing-set-monad body)
  (splicing-syntax-parameterize
   ([yield-meaning (λ (stx) (syntax-parse stx [(_ e)
                                               (syntax/loc stx
                                                 (values target-σ (∪1 target-cs e)))]))])
   body))

(define-syntax-rule (with-σ-passing-generators body)
  (splicing-syntax-parameterize
   ([yield-meaning (λ (stx) (syntax-parse stx [(_ e)
                                               (syntax/loc stx
                                                 (begin (real-yield e) target-σ))]))])
   body))

(define-syntax-rule (with-mutable-worklist body)
  (splicing-syntax-parameterize
   ([yield-meaning yield!])
   body))

(define-syntax-rule (with-lazy body)
  (splicing-syntax-parameterize
   ([delay (make-rename-transformer #'lazy-delay)]
    [force (make-rename-transformer #'lazy-force)])
   body))

(define-syntax-rule (with-lazy-σ-∆s body)
  (splicing-syntax-parameterize
   ([delay (make-rename-transformer #'lazy-delay)]
    [force (make-rename-transformer #'lazy-force-σ-∆s)])
   body))

(define-syntax-rule (with-0-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0)])
   body))

(define-syntax-rule (with-0-σ-∆s-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-∆s-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0)])
   body))

(define-syntax-rule (with-0-ctx/prealloc body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-0)]
    [make-var-contour (make-rename-transformer #'make-var-contour-0-prealloc)])
   body))

(define-syntax-rule (with-∞-ctx body)
  (splicing-syntax-parameterize
   ([bind (make-rename-transformer #'bind-∞)]
    [make-var-contour (make-rename-transformer #'make-var-contour-k)])
   body))

(define-syntax-rule (with-whole-σ body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-whole)]
    [bind-join* (make-rename-transformer #'bind-join*-whole)]
    [getter (make-rename-transformer #'hash-getter)]
    ;; separate out this force?
    [force (make-rename-transformer #'lazy-force)])
   body))

(define-syntax-rule (with-mutable-store body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join!)]
    [bind-join* (make-rename-transformer #'bind-join*!)]
    [getter (make-rename-transformer #'global-vector-getter)]
    ;; separate out this force?
    [force (make-rename-transformer #'lazy-force!)])
   body))

(define-syntax-rule (with-σ-∆s body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-∆s)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s)]
    [getter (make-rename-transformer #'top-hash-getter)]
    [force (make-rename-transformer #'lazy-force-σ-∆s)])
   body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Potpourris of evaluators
#|
;; Compiled wide concrete store-passing set monad
(with-lazy
 (with-∞-ctx
  (with-whole-σ
   (with-narrow-set-monad
    (with-concrete
      (mk-analysis #:aval lazy-eval/c #:ans ans/c
                   #:σ-passing ;; not really passing, but carried.
                   #:set-monad #:kcfa +inf.0
                   #:compiled))))))

(provide lazy-eval/c)
(with-lazy
 (with-∞-ctx
  (with-whole-σ
   (with-narrow-set-monad
    (with-concrete
      (mk-analysis #:aval lazy-eval #:ans ans
                   #:σ-passing
                   #:set-monad #:kcfa +inf.0))))))
(provide lazy-eval/c)

(mk-set-fixpoint^ fix eval-set-fixpoint^ ans^?)
(with-lazy
 (with-∞-ctx
  (with-whole-σ
   (with-σ-passing-set-monad
    (with-concrete
      (mk-analysis #:aval lazy-eval^/c #:ans ans^
                   #:fixpoint eval-set-fixpoint^
                   #:compiled #:set-monad #:wide #:σ-passing
                   #:kcfa +inf.0))))))
(provide lazy-eval^/c)
|#

(mk-set-fixpoint^ fix 0cfa-set-fixpoint^/c 0cfa-ans^/c?)
(with-lazy
 (with-0-ctx
  (with-whole-σ
   (with-σ-passing-set-monad
    (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c #:ans 0cfa-ans^/c
                   #:fixpoint 0cfa-set-fixpoint^/c
                   #:σ-passing
                   #:compiled #:wide #:set-monad))))))
(provide lazy-0cfa^/c)

(mk-set-fixpoint^ fix 0cfa-set-fixpoint^ 0cfa-ans^?)
(with-lazy
 (with-0-ctx
  (with-whole-σ
   (with-σ-passing-set-monad
    (with-abstract
      (mk-analysis #:aval lazy-0cfa^ #:ans 0cfa-ans^
                   #:fixpoint 0cfa-set-fixpoint^
                   #:σ-passing
                   #:wide #:set-monad))))))
(provide lazy-0cfa^)

(mk-generator/wide/σ-∆s-fixpoint lazy-0cfa-gen^-fix gen-ans^?)
(with-lazy-σ-∆s
 (with-0-σ-∆s-ctx
  (with-σ-∆s
   (with-σ-passing-generators
    (with-abstract
      (mk-analysis #:aval lazy-0cfa^-gen-σ-∆s #:ans gen-ans^
                   #:fixpoint lazy-0cfa-gen^-fix
                   #:σ-∆s
                   #:wide #:generators))))))
(provide lazy-0cfa^-gen-σ-∆s)

(mk-generator/wide/σ-∆s-fixpoint lazy-0cfa-gen^-fix/c gen-ans^/c?)
(with-lazy-σ-∆s
 (with-0-σ-∆s-ctx
  (with-σ-∆s
   (with-σ-passing-generators
    (with-abstract
      (mk-analysis #:aval lazy-0cfa^-gen-σ-∆s/c #:ans gen-ans^/c
                   #:fixpoint lazy-0cfa-gen^-fix/c
                   #:σ-∆s
                   #:compiled #:wide #:generators))))))
(provide lazy-0cfa^-gen-σ-∆s/c)

;; FIXME bind-join conses onto a hash rather than a list
#;#;#;
(mk-∆-fix^ lazy-0cfa∆^-fixpoint 0cfa∆-ans^?)
(with-lazy
 (with-0-ctx
  (with-σ-∆s
   (with-σ-passing-set-monad
    (with-abstract
      (mk-analysis #:aval lazy-0cfa∆/c #:ans 0cfa∆-ans^
                   #:fixpoint lazy-0cfa∆^-fixpoint
                   #:wide #:σ-∆s #:set-monad
                   #:compiled))))))
(provide lazy-0cfa∆/c)
#;#;#;#;
(mk-prealloc^-fixpoint prealloc/imperative-fixpoint prealloc-ans? prealloc-ans-v #t)
(with-lazy
 (with-0-ctx/prealloc
  (with-mutable-store
   (with-mutable-worklist
    (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c!-prepared #:ans prealloc-ans
                   #:fixpoint prealloc/imperative-fixpoint
                   #:pre-alloc #:compiled #:imperative #:wide))))))
(define (lazy-0cfa^/c! sexp)
  (lazy-0cfa^/c!-prepared (prepare-prealloc parse-prog sexp)))
(provide lazy-0cfa^/c!)
