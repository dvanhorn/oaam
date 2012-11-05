#lang racket
(require "do.rkt" "data.rkt" "primitives.rkt" racket/stxparam racket/splicing)
(provide with-nonsparse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-sparse analyses do not need to accumulate actions
(define-syntax-rule (bind-get-nonsparse (res σ a) body)
  (let ([res (getter σ a)]) body))

(define-syntax-rule (bind-force-nonsparse (res σ v) body)
  (let ([res (force σ v)]) body))

(define-syntax-rule (bind-big-alias-nonsparse (σ* σ alias all-to-alias) body)
  (bind-join (σ* σ alias (for/fold ([acc nothing]) ([a (in-list all-to-alias)])
                           (⊓ acc (getter σ a))))
             body))
(define-syntax-rule (bind-alias*-nonsparse (σ* σ aliases all-to-alias) body)
  (bind-join* (σ* σ aliases (for/list ([a (in-list all-to-alias)]) (getter σ a))) body))

(define-syntax-rule (with-nonsparse body)
  (splicing-syntax-parameterize
   ([bind-get (make-rename-transformer #'bind-get-nonsparse)]
    [bind-force (make-rename-transformer #'bind-force-nonsparse)]
    [bind-big-alias (make-rename-transformer #'bind-big-alias-nonsparse)]
    [bind-alias* (make-rename-transformer #'bind-alias*-nonsparse)])
   body))
