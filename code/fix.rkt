#lang racket
(require "notation.rkt" "graph.rkt" (for-syntax racket/stxparam))
(provide mk-fix fix appl)

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