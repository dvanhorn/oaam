#lang racket

(require (for-syntax syntax/parse))
(provide for/append for/union for*/union for/set for*/set
         define-simple-macro* hash-reverse and
         (for-syntax ops)
         (rename-out [safer-match match]
                     [safer-match* match*])
         add1/debug
         ∅ ∅? ¬∅? ∪ ∩ ⊆? ∖ ∪1 ∪/l ∖1 ∖/l ∈)

(define-syntax (safer-match stx)
  (syntax-parse stx
    [(_ e others ...)
     #`(match e others ... [t (error 'match "Bad match ~a ~a" t '#,stx)])]))
(define-syntax (safer-match* stx)
  (syntax-parse stx
    [(_ e [(pats ...) rhs ...] ...)
     (with-syntax ([(t ...) (generate-temporaries (car (syntax->list #'((pats ...) ...))))])
       #`(match* e
           [(pats ...) rhs ...] ...
           [(t ...) (error 'match "Bad match ~a ~a" (list t ...) '#,stx)]))]))

(define (add1/debug n from)
  (unless (number? n)
    (error 'add1 "Bad input from ~a" from))
  (add1 n))

;; define-simple-macro does not have an implicit quasisyntax.
(define-syntax (define-simple-macro* stx)
  (syntax-parse stx
    [(_ (name:id . pattern) directives ... template)
     (syntax/loc stx
       (define-syntax (name syn)
         (syntax-parse syn
           [(name . pattern) directives ... (quasisyntax/loc syn template)])))]))
;; Because I want binding!!
(define-syntax (and stx)
  (syntax-parse stx
    [(_) #'#t]
    [(_ e) #'e]
    [(_ #:bind x:id e:expr es ...+) #'(let ([x e]) (if x (and es ...) #f))]
    [(_ e:expr es ...) #'(if e (and es ...) #f)]))

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

(define-simple-macro* (for/union (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro* (for*/union (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪ o.res (let () body ...))))
(define-simple-macro* (for/set (~var o (ops #'∅)) guards body ...+)
  (for/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))
(define-simple-macro* (for*/set (~var o (ops #'∅)) guards body ...+)
  (for*/fold ([o.res o.init]) guards (∪1 o.res (let () body ...))))
