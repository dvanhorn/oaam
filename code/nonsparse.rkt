#lang racket
(require "do.rkt" "data.rkt" "primitives.rkt" racket/stxparam racket/splicing)
(provide with-nonsparse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-sparse analyses do not need to accumulate actions
(define-syntax-rule (bind-get-nonsparse (res a) body)
  (let ([res (getter a)]) body))

(define-syntax-rule (bind-force-nonsparse (res v) body)
  (let ([res (force v)]) body))

(define-syntax-rule (bind-delay-nonsparse (res a) body)
  (let ([res (delay a)]) body))

(define-syntax-rule (bind-big-alias-nonsparse (alias all-to-alias) body)
  (bind-join (alias (for/fold ([acc nothing]) ([a (in-list all-to-alias)])
                      (⊓ acc (getter a))))
             body))
(define-syntax-rule (bind-alias*-nonsparse (aliases all-to-alias) body)
  (bind-join* (aliases (for/list ([a (in-list all-to-alias)]) (getter a))) body))

(define-syntax-rule (with-nonsparse body)
  (splicing-syntax-parameterize
   ([bind-get (make-rename-transformer #'bind-get-nonsparse)]
    [bind-force (make-rename-transformer #'bind-force-nonsparse)]
    [bind-delay (make-rename-transformer #'bind-delay-nonsparse)]
    [bind-big-alias (make-rename-transformer #'bind-big-alias-nonsparse)]
    [bind-alias* (make-rename-transformer #'bind-alias*-nonsparse)])
   body))
