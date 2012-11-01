#lang racket
(require "do.rkt" "data.rkt" "primitives.rkt" racket/stxparam racket/splicing)
(provide (struct-out use)
         (struct-out change)
         with-nonsparse with-sparse)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sparse analyses accumulate actions on uses and changes of addresses.
(struct use (addr) #:prefab)
(struct change (addr) #:prefab)

(define-syntax-rule (bind-get-sparse (res σ a) body)
  (let ([res (getter σ a)]
        [actions (∪1 target-actions (use a))])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body)))

(define-syntax-rule (bind-force-sparse (res σ v) body)
  (let ([res (force σ v)]
        [actions (∪1 target-actions (change a))])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      body)))

(define-syntax-rule (bind-big-alias-sparse (σ* σ alias all-to-alias) body)
  (let-values ([(actions val)
                (for/fold ([actions target-actions]
                           [val nothing]) ([to-alias (in-list all-to-alias)])
                  (values (∪1 actions (use to-alias))
                          (⊓ val (getter σ to-alias))))])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      (bind-join (σ* σ alias val) body))))

(define-syntax-rule (bind-alias*-sparse (σ* σ aliases all-to-alias) body)
  (let-values ([(actions rev-aliases rev-vals)
                (for/fold ([actions target-actions] [raliases '()] [vals '()])
                    ([alias (in-list aliases)]
                     [to-alias (in-list all-to-alias)])
                  (values (∪ actions (set (use to-alias) (change alias)))
                          ;; XXX: icky intermediate lists.
                          (cons alias raliases)
                          (cons (getter σ to-alias) vals)))])
    (syntax-parameterize ([target-actions (make-rename-transformer #'actions)])
      (bind-join* (σ* σ rev-aliases rev-vals) body))))

(define-syntax-rule (with-nonsparse body)
  (splicing-syntax-parameterize
   ([bind-get (make-rename-transformer #'bind-get-nonsparse)]
    [bind-force (make-rename-transformer #'bind-force-nonsparse)]
    [bind-big-alias (make-rename-transformer #'bind-big-alias-nonsparse)]
    [bind-alias* (make-rename-transformer #'bind-alias*-nonsparse)])
   body))

(define-syntax-rule (with-sparse body)
  (splicing-syntax-parameterize
   ([bind-get (make-rename-transformer #'bind-get-sparse)]
    [bind-force (make-rename-transformer #'bind-force-sparse)]
    [bind-alias (make-rename-transformer #'bind-alias-sparse)]
    [bind-big-alias (make-rename-transformer #'bind-big-alias-nonsparse)]
    [bind-alias* (make-rename-transformer #'bind-alias*-nonsparse)])
   body))
