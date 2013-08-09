#lang racket
(require racket/unit (except-in "notation.rkt" ∪ ∩))
(require racket/trace)

(provide TCon-deriv^ TCon-deriv@ weak-eq^
         may must
         for/∧ for*/∧
         ¬ · kl bind ε
         call ret !call !ret
         $ □ Any label
         (rename-out [∪ tor] [∩ tand] )
         (struct-out kl)
         (struct-out tl)
         M⊥
         ε)

(struct -unmapped ()) (define unmapped (-unmapped))

;; Temporal contracts
(struct ¬ (T) #:transparent)
(struct · (T₀ T₁) #:transparent)
(struct kl (T) #:transparent)
(struct bind (B T) #:transparent)
(struct ∪ (Ts) #:transparent)
(struct ∩ (Ts) #:transparent)
(struct -ε () #:transparent) (define ε (-ε))
(define T⊥ (∪ ∅)) ;; empty contract
(define Σ̂* (∩ ∅))
(define (∂? x)
  (or (¬? x) (·? x) (event? x) (kl? x) (bind? x) (∪? x) (∩? x)))
(define (ð? x)
  (match x
    [(or (cons (? ∂?) (? hash?))
         (? ∂?)
         (¬ (? ð?))
         (· (? ð?) (? ð?))
         (kl (? ð?))
         (== ε eq?))
     #t]
    [(or (∪ Ts) (∩ Ts)) (for/and ([T (in-set Ts)]) (ð? T))]
    [_ #f]))

(struct constructed (c data) #:transparent)
(struct !constructed (c data) #:transparent)
(struct -Any () #:transparent) (define Any (-Any))
(struct $ (x) #:transparent)
(struct □ (x) #:transparent)
(struct label (ℓ) #:transparent)

;; Niceties for writing temporal contracts using the general language of patterns.
(define (call nf pas) (constructed 'call (cons nf pas)))
(define (ret nf pv) (constructed 'call (list nf pv)))
(define (!call nf pas) (!constructed 'call (cons nf pas)))
(define (!ret nf pv) (!constructed 'ret (list nf pv)))
(define/match (event? x)
  [((constructed 'ret (list _ _))) #t]
  [((!constructed 'ret (list _ _))) #t]
  [((constructed 'call (list-rest _ _))) #t]
  [((!constructed 'call (list-rest _ _))) #t]
  [(_) #f])

;; 3-valued logic
(struct -must ()) (define must (-must))
(struct -may ()) (define may (-may))

(define/match (∧ t₀ t₁)
  [((== must eq?) (== must eq?)) must]
  [(#f _) #f]
  [(_ #f) #f]
  [(_ _) may])

(define/match (∨ t₀ t₁)
  [(#f #f) #f]
  [((== must eq?) _) must]
  [(_ (== must eq?)) must]
  [(_ _) may])

(define-syntax-rule (for/∧ guards body)
  (for/fold ([res must]) guards (∧ res (let () body))))
(define-syntax-rule (for*/∧ guards body)
  (for*/fold ([res must]) guards (∧ res (let () body))))

;; valuations with updated bindings
(struct mres (t ρ) #:transparent)

;; Top level
(struct tl (T t) #:transparent)
(define M⊥ (tl T⊥ must))
(define Σ* (tl Σ̂* must))
(define Mε (tl ε must))

(define/match (·simpl T₀ T₁)
  [((== ε eq?) T₁) T₁]
  [(T₀ (== ε eq?)) T₀]
  [((== T⊥ eq?) _) T⊥]
  [(_ (== T⊥ eq?)) T⊥]
  ;; Right-associate
  [((· T₀₀ T₀₁) T₁) (·simpl T₀₀ (·simpl T₀₁ T₁))]
  ;; No simplifications
  [(T₀ T₁) (· T₀ T₁)])

;; Flatten ∪s and ∪s into one big ∪ or ∩.
(define (flat-collect pred extract Ts)
  (let recur ([Ts Ts] [a ∅])
    (for/fold ([a a]) ([T (in-set Ts)])
      (if (pred T)
          (recur (extract T) a)
          (set-add a T)))))
;(trace flat-collect);
(define (∪simpl Ts)
  (define Ts′ (flat-collect ∪? ∪-Ts Ts))
  (cond [(set-empty? Ts′) T⊥]
        [(= (set-count Ts′) 1) (set-first Ts′)]
        [else (∪ Ts′)]))

(define (∩simpl Ts)
  (define Ts′ (flat-collect ∩? ∩-Ts Ts))
  (cond [(set-empty? Ts′) Σ̂*]
        [(= (set-count Ts′) 1) (set-first Ts′)]
        [else (∩ Ts′)]))

;; Combine bindings giving preference to the right hash.
(define (◃ ρ₀ ρ₁)
  (for/fold ([ρ ρ₀]) ([(k v) (in-hash ρ₁)])
    (hash-set ρ k v)))

(define (⨅ S f)
  (let/ec break
    (define-values (t ρ)
      (for/fold ([t must]
                 [ρ #hasheq()])
          ([s (in-set S)])
        (match (f s)
          [#f (break #f)]
          [(mres t′ ρ′) (values (∧ t t′) (ρ . ◃ . ρ′))]
          [err (error '⨅ "Bad res ~a" err)])))
    (mres t ρ)))

(define (⨅/lst f L R)
  (let/ec break
    (define-values (t ρ)
      (for/fold ([t must]
                 [ρ #hasheq()])
          ([l (in-list L)]
           [r (in-list R)])
        (match (f l r)
          [#f (break #f)]
          [(mres t′ ρ′) (values (∧ t t′) (ρ . ◃ . ρ′))]
          [err (error '⨅ "Bad res ~a" err)])))
    (mres t ρ)))

;; Is the contract nullable?
(define (ν? T)
  (match T
    [(or (kl _) (== ε eq?)) #t]
    [(· T₀ T₁) (and (ν? T₀) (ν? T₁))]
    [(∪ Ts) (for/or ([T (in-set Ts)]) (ν? T))]
    [(∩ Ts) (for/and ([T (in-set Ts)]) (ν? T))]
    [(¬ T) #t]
    [(cons T ρ) (ν? T)]
    [_ #f])) ;; bind, event, nonevent

(define/match (negate T)
  [((¬ T)) T]
  [(T) (¬ T)])

(define-signature weak-eq^ (≃ matchℓ?))
(define-signature TCon-deriv^ (run ð))

(define (matches≃ ≃ matchℓ?)
  (define (matches P A γ)
    (define (matches1 P) (matches P A γ))
    (define (matches2 P A) (matches P A γ))
    (match P
      [(? set?) (⨅ P matches1)]
      [(!constructed kind pats)
       (match (matches1 (constructed kind pats))
         [(mres (== must eq?) _) #f]
         [#f (mres must γ)]
         [(mres _ γ′) (mres may γ)]
         [err (error 'matches "Bad ! ~a" err)])]
      [(constructed kind pats)
       (match A
         [(constructed (== kind eq?) data)
          (⨅/lst matches2 pats data)]
         [_ #f])]
      [(== Any eq?) (mres must γ)]
      [(label ℓ)
       (and (matchℓ? A ℓ)
            (mres must γ))]
      [(□ x) (mres must (hash-set γ x A))]
      [($ x)
       (match (hash-ref γ x unmapped)
         [(== unmapped eq?) #f]
         [v (matches2 v A)])]
      [v (match (≃ v A)
           [#f #f]
           [t (mres t γ)])]))
  matches)

(define-unit TCon-deriv@
  (import weak-eq^)
   (export TCon-deriv^)
   (define matches (matches≃ ≃ matchℓ?))

   ;; Negation differs because it waits until we have a /full/ match.
   ;; Thus, we do a nullability check to see if it is satisfied.
   ;; If a may state, we stay may only if the contract is nullable.
   ;; FIXME: Need a may fail (#f)
   (define (¬p rec form T)
     (match (rec T)
       [(== M⊥ eq?) Σ*]
       [(tl T′ (== must eq?))
        (if (ν? T′)
            Mε
            (form (negate T′) must))]
       [(tl T′ t′) (form (negate T′) (if (ν? T′) may must))]
       [M (error '¬p "oops3 ~a" M)]))

   (define (·p rec form T₀ T₁)
     (if (ν? T₀)
         (match (rec T₀)
           [(== M⊥ eq?) (rec T₁)] ;; Might be able to pass T₀ from nullability
           [(tl T₀′ t′)
            (match (rec T₁)
              [(== M⊥ eq?) (form (·simpl T₀′ T₁) t′)]
              ;; Both derivatives matched.
              [(tl T₁′ t″) (form (∪simpl (set (·simpl T₀′ T₁) T₁′)) (∨ t′ t″))]
              [M (error '·p "oops4 ~a" M)])]
           [M (error '·p "oops5 ~a" M)])
         (match (rec T₀)
           [(== M⊥ eq?) M⊥]
           [(tl T′ t′) (form (·simpl T′ T₁) t′)]
           [M (error '·p "oops6 ~a" M)])))

   (define (klp rec form T′ T)
     (match (rec T′)
       [(== M⊥ eq?) M⊥]
       [(tl T″ t′) (form (·simpl T″ T) t′)]
       [M (error 'klp "oops7 ~a" M)]))

   ;; Match some
   (define (∪p rec form Ts)
     (let/ec break
       (define-values (t′ Ts′)
         (for/fold ([t must] [Ts′ ∅]) ([T (in-set Ts)])
           (match (rec T)
             [(== Σ* eq?) (break Σ*)]
             [(== M⊥ eq?) (values t Ts′)] ;; shortcut
             [(tl T′ t′) (values (∨ t t′) (set-add Ts′ T′))]
             [M (error '∪p "oops8 ~a" M)])))
       (if (set-empty? Ts′)
           M⊥
           (form (∪simpl Ts′) t′))))

   ;; Match all
   (define (∩p rec form Ts)
     (let/ec break
       (define-values (t′ Ts′)
         (for/fold ([t must] [Ts′ ∅]) ([T (in-set Ts)])
           (match (rec T)
             [(== M⊥ eq?) (break M⊥)]
             [(== Σ* eq?) (values t Ts′)] ;; shortcut
             [(tl T′ t′) (values (∧ t t′) (set-add Ts′ T′))]
             [M (error '∩p "oops9 ~a" M)])))
       (if (set-empty? Ts′)
           Σ*
           (form (∩ Ts′) t′))))

   (define (bindp B A T ρ)
     (match (matches B A ρ)
       [#f M⊥]
       [(mres t′ ρ′) (tl (cons T ρ′) t′)]
       [M (error '∂ "oops10 ~a" M)]))
   
   (define (patp pat A ρ)
     (match (matches pat A ρ)
       [#f M⊥]
       [(mres t ρ′) (tl ε t)]
       [M (error '∂ "oops11 ~a" M)]))
   
   (define ρ₀ #hasheq())

   ;; Top level temporal contracts with distributed ρs.
   (define (ð A T)
     (define (ð1 T) (ð A T))
     (match T
       [(== Σ̂* eq?) (tl T must)]
       [(or (== T⊥ eq?) (== ε eq?)) M⊥]
       [(cons T ρ) (∂ A T ρ)]
       [(· T₀ T₁) (·p ð1 tl T₀ T₁)]
       [(¬ T) (¬p ð1 tl T)]
       [(kl T′) (klp ð1 tl T′ T)]
       [(∪ Ts) (∪p ð1 tl Ts)]
       [(∩ Ts) (∩p ð1 tl Ts)]
       ;; Top level! Can't have previous bindings. T can't have closures.
       [(bind B T) (bindp B A T ρ₀)]
       [Aor!A (patp Aor!A A ρ₀)]))

   (define (∂ A T ρ)
     (define (∂1 T) (∂ A T ρ))
     (define (tlρ T t) (tl (cons T ρ) t))
     (match T
       [(== Σ̂* eq?) (tl T must)]
       [(or (== T⊥ eq?) (== ε eq?)) M⊥]
       [(· T₀ T₁) (·p ∂1 tlρ T₀ T₁)]
       [(¬ T) (¬p ∂1 tlρ T)]
       [(kl T′) (klp ∂1 tlρ T′ T)]
       [(∪ Ts) (∪p ∂1 tlρ Ts)]
       [(∩ Ts) (∩p ∂1 tlρ Ts)]
       ;; dseq
       [(bind B T) (bindp B A T ρ)]
       ;; Event/unevent
       [Aor!A (patp Aor!A A ρ)]))

   (define (run* Tt π)
     (match π
       ['() Tt]
       [(cons A π) 
        (match Tt
          [(tl T t) (run* (ð A T) π)]
          [(== M⊥ eq?) M⊥]
          [M (error 'run* "oops12 ~a" M)])]
       [err (error 'run* "Bad ~a" err)]))
   (define run run*))

(define-unit concrete@
  (import)
   (export weak-eq^)
   (define (≃ x y) (and (equal? x y) must))
   (define matchℓ? eq?))

(define-values/invoke-unit/infer (export TCon-deriv^) (link concrete@ TCon-deriv@))
