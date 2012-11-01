#lang racket
(require "do.rkt" "env.rkt" "notation.rkt" "primitives.rkt" racket/splicing racket/stxparam
         "store-passing.rkt" "context.rkt")
(provide bind-join-∆s bind-join*-∆s mk-∆-fix^ with-σ-∆s)

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

(define-simple-macro* (bind-join-∆s (∆s* ∆s a vs) body)
  (let ([∆s* (cons (cons a vs) ∆s)]) #,(bind-rest #'∆s* #'body)))
(define-simple-macro* (bind-join*-∆s (∆s* ∆s as vss) body)
  (let ([∆s* (map2-append cons ∆s as vss)]) #,(bind-rest #'∆s* #'body)))

(define-syntax-rule (top-hash-getter thgσ a)
  (hash-ref top-σ a (λ () (error 'top-hash-getter "Unbound address ~a in store ~a" a top-σ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Wide fixpoint for σ-∆s

(define-syntax-rule (mk-∆-fix^ name ans^?)
  (define-syntax-rule (name stepper fst)
    (let-values ([(∆ cs) fst])
     (define seen (make-hash))
     (define todo (set (cons (update ∆ (hash)) cs)))
     (let loop ()
       (cond [(∅? todo) (for/set ([(c δσ) (in-hash seen)]
                                  #:when (ans^? c))
                          (cons δσ c))]
             [else (define old-todo todo)
                   (set! todo ∅)
                   (for* ([σ×cs (in-set old-todo)]
                          [σp (in-value (car σ×cs))]
                          [c (in-set (cdr σ×cs))]
                          [last-σ (in-value (hash-ref seen c (hash)))]
                          #:unless (equal? last-σ σp))
                     ;; This state's store monotonically increases
                     (hash-set! seen c (join-store σp last-σ))
                     ;; Add the updated store with next steps to workset
                     (define-values (∆ cs*) (stepper (cons σp c)))
                     (set! todo (∪1 todo (cons (update ∆ σp) cs*))))
                   (loop)])))))

(define-syntax-rule (with-σ-∆s body)
  (splicing-syntax-parameterize
   ([bind-join (make-rename-transformer #'bind-join-∆s)]
    [bind-join* (make-rename-transformer #'bind-join*-∆s)]
    [getter (make-rename-transformer #'top-hash-getter)])
   body))
