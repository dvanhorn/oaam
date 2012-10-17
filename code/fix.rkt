#lang racket
(require "notation.rkt")
(provide fix appl)

;; appl : (∀ (X) ((X -> (Setof X)) -> ((Setof X) -> (Setof X))))
(define ((appl f) s)
  (for/union ([x (in-set s)]) (f x)))

;; Calculate fixpoint of (appl f).
;; fix : (∀ (X) ((X -> (Setof X)) (Setof X) -> (Setof X)))
(define (fix f s)
  (let loop ((accum (set)) (front s))
    (cond [(set-empty? front) accum]
          [else (define new-front ((appl f) front))
                (loop (∪ accum front) (new-front . ∖ . accum))])))
