#lang racket
(require "notation.rkt")
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

(define-syntax-rule (mk-fix name ans? ans-v)
  (define (name step fst)
    (define ss (fix step fst))
    (for/set ([s ss] #:when (ans? s)) (ans-v s))))