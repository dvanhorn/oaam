#lang racket
(require "notation.rkt" "graph.rkt" racket/stxparam)
(provide mk-fix fix appl fix-t fix-t2)

;; appl : (∀ (X) ((X -> (Setof X)) -> ((Setof X) -> (Setof X))))
(define ((appl f) s)
  (for/union ([x (in-set s)]) (f x)))

;; Calculate fixpoint of (appl f).
;; fix : (∀ (X) ((X -> (Setof X)) (Setof X) -> (Setof X)))
(define (fix f s)
  (let loop ((accum ∅) (front s))
    (cond [(∅? front) accum]
          [else (define new-front ((appl f) front))
                (loop (∪ accum front) (new-front . ∖ . accum))])))

(define (fix-t f σ cs)
  (let loop ([accum ∅] [front cs] [σ σ] [t 0] [Σ (list σ)])
    (cond [(∅? front) (values Σ accum)]
          [else (define-values (σ* stepped) (f σ front))
                (define-values (t* Σ*)
                  (if (equal? σ σ*)
                      (values t Σ)
                      (values (add1 t) (cons σ* Σ))))
                (define-values (new-accum new-front)
                  (for*/fold ([new-accum accum]
                              [new-front ∅])
                      ([c (in-set stepped)]
                       [s (in-value (cons t* c))]
                       #:unless (set-member? accum s))
                    (values (∪1 new-accum s) (∪1 new-front c))))
                (loop new-accum new-front σ* t* Σ*)])))

(define (fix-t2 f σ cs)
  (let loop ([accum ∅] [front cs] [σ σ] [t 0] [Σ (list σ)])
    (cond [(∅? front) (values Σ accum)]
          [else (define-values (σ* ∆? stepped) (f σ front))
                (define-values (t* Σ*)
                  (if ∆?
                      (values (add1 t) (cons σ* Σ))
                      (values t Σ)))
                (define-values (new-accum new-front)
                  (for*/fold ([new-accum accum]
                              [new-front ∅])
                      ([c (in-set stepped)]
                       [s (in-value (cons t* c))]
                       #:unless (set-member? accum s))
                    (values (∪1 new-accum s) (∪1 new-front c))))
                (loop new-accum new-front σ* t* Σ*)])))

(define-simple-macro* (mk-fix name ans? ans-v)
  (define (name step fst)
    (define graph (make-hash))
    (define ss (fix #,(if (syntax-parameter-value #'generate-graph?)
                          #'(λ (s)
                               (define res (step s))
                               (for ([s* (in-set res)])
                                 (add-edge! graph s s*))
                               res)
                          #'step)
                    fst))
    #,@(if (syntax-parameter-value #'generate-graph?) #'((dump-dot graph)) #'())
    (values (format "State count: ~a" (set-count ss))
            (for/set ([s ss] #:when (ans? s)) (ans-v s)))))