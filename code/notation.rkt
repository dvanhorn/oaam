#lang racket

(require (for-syntax syntax/parse))
(provide for/append for/union for*/union for/set for*/set
         and0
         define-simple-macro* hash-reverse hash-add hash-union set-map
         ∅ ∅? ¬∅? ∪ ∩ ⊆? ∖ ∪1 ∪/l ∖1 ∖/l ∈)

;; define-simple-macro does not have an implicit quasisyntax.
(define-syntax (define-simple-macro* stx)
  (syntax-parse stx
    [(_ (name:id . pattern) directives ... template-code)
     (syntax/loc stx
       (define-syntax (name syn)
         (syntax-parse syn
           [(name . pattern) directives ... (quasisyntax/loc syn template-code)])))]))

;; Perform an and but return the first value anded.
(define-syntax and0
  (syntax-rules ()
    [(_) #t]
    [(_ e) e]
    [(_ e es ...) (let ([x e]) (and x es ... x))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for/union

(begin-for-syntax
 (define-splicing-syntax-class (ops initial)
   #:attributes (init res)
   (pattern (~seq (~or (~optional (~seq #:initial init:expr)
                                  #:defaults ([init initial]))
                       (~optional (~seq #:res res:id)
                                  #:defaults ([res #'acc]))) ...))))

(define-simple-macro* (for/append (~var o (ops #''())) guards body ...+)
  (for/fold ([o.res o.init]) guards (append (let () body ...) o.res)))

;; Set notations
(define-values (∅ ∅? ¬∅? ∪ ∩ ⊆? ∖ ∪1 ∪/l ∖1 ∖/l ∈)
  (let ([set-add*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-add s x)))]
        [set-remove*
         (λ (s xs) (for/fold ([s s]) ([x (in-list xs)]) (set-remove s x)))]
        [in? (λ (x s) (set-member? s x))])
    (values (set) set-empty? (λ (s) (not (set-empty? s)))
            set-union set-intersect subset? set-subtract
            set-add set-add*
            set-remove set-remove* in?)))

(define (hash-reverse h)
  (for/hash ([(k v) (in-hash h)])
    (values v k)))

(define (hash-add h k v)
  (hash-set h k (∪1 (hash-ref h k ∅) v)))
(define (hash-union h k v)
  (hash-set h k (∪ (hash-ref h k ∅) v)))

(define (set-map f s)
  (for/set ([a (in-set s)]) (f a)))

(define-simple-macro* (for/union (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro* (for*/union (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro* (for/set (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))
(define-simple-macro* (for*/set (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))
