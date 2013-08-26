#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "imperative.rkt" "store-passing.rkt"
         (rename-in racket/generator [yield real-yield]))
(provide mk-generator/wide/σ-∆s-fixpoint
         mk-generator/wide/imperative-fixpoint
         with-σ-passing-generators
         with-global-σ-generators)

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
       [(cons gσ cs)
        (define-values (cs* ∆)
          (for/fold ([cs* ∅] [∆* '()])
              ([c cs] #:unless (ans? c))
            (pull (step (cons gσ c)) ∆* cs*)))
        (cons (update ∆ gσ) (set-union cs cs*))])))

(define-syntax-rule (mk-generator/wide/σ-∆s-fixpoint name ans? touches)
  (define-syntax-rule (name step fst)
    (let ()
      (define wide-step (σ-∆s/generator/wide-step-specialized step ans?))
      (define clean-σ (restrict-to-reachable touches))
      (define-values (cs ∆) (pull fst '() ∅))
      (define fst-s (cons (update ∆ empty-σ) cs))
      (define snd (wide-step fst-s))
      (let loop ((next snd) (prev fst-s))
        (cond [(equal? next prev)
               (define answers 
                       (for/set ([c (cdr prev)]
                                 #:when (ans? c))
                         c))
               (values (format "State count: ~a" (set-count (cdr prev)))
                       (clean-σ (car prev) answers)
                       answers)]
              [else (loop (wide-step next) next)])))))

(define-syntax-rule (pull-global gen cs-base)
  (for/set #:initial cs-base
      ([c (in-producer gen (λ (x) (eq? 'done x)))])
    c))

(define-syntax-rule (imperative/generator/wide-step-specialized step ans?)
  (match-lambda
   [(cons σ-count cs)
    (define cs*
      (for/fold ([cs* ∅])
          ([c cs] #:unless (ans? c))
        (pull-global (step c) cs*)))
    (cons unions (∪ cs cs*))]))

(define-syntax-rule (mk-generator/wide/imperative-fixpoint name ans? ans-v touches)
  (define-syntax-rule (name step fst)
    (let ()
      (define wide-step (imperative/generator/wide-step-specialized step ans?))
      (define clean-σ (restrict-to-reachable touches))
      (reset-globals! (make-hash))
      (define cs (pull-global fst ∅))
      (define fst-s (cons unions cs))
      (define snd (wide-step fst-s))
      (let loop ((next snd) (prev fst-s))
        (cond [(equal? next prev)
               (define answers (for/set ([c (cdr prev)]
                                         #:when (ans? c))
                                 (ans-v c)))
               (values (format "State count: ~a" (set-count (cdr prev)))
                       (clean-σ global-σ answers)
                       answers)]
              [else
               (loop (wide-step next) next)])))))

(define-syntax-rule (with-σ-passing-generators body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (begin (real-yield e) target-σ)])])
   body))

(define-syntax-rule (with-global-σ-generators body)
  (splicing-syntax-parameterize
   ([yield-meaning (syntax-rules () [(_ e) (real-yield e)])])
   body))