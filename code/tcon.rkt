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
         simple
         (struct-out kl)
         (struct-out tl)         
         M⊥
         ε)

(struct -unmapped ()) (define unmapped (-unmapped))

;; Temporal contracts
(struct simple (T) #:transparent) ;; wrapper for Tcons without bindings.
(struct closed (T ρ) #:transparent) ;; like above, but closes free variables.
(struct ¬ (T) #:transparent)
(struct · (T₀ T₁) #:transparent)
(struct kl (T) #:transparent)
(struct bind (B T) #:transparent)
(struct ∪ (Ts) #:transparent)
(struct ∩ (Ts) #:transparent)
(struct -ε () #:transparent) (define ε (-ε)) (define Tε (simple ε))
(define T⊥ (∪ ∅)) (define ST⊥ (simple T⊥)) ;; empty contract
(define Σ̂* (∩ ∅)) (define SΣ̂* (simple Σ̂*))
(define (∂? x)
  (or (¬? x) (·? x) (event? x) (kl? x) (bind? x) (∪? x) (∩? x) (eq? x ε)))
(define (ð? x)
  (match x
    [(or (simple (? ∂?))
         (closed (? ∂?) (? hash?))
         (¬ (? ð?))
         (· (? ð?) (? ð?))
         (kl (? ð?)))
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
(define M⊥ (tl ST⊥ must))
(define Σ* (tl SΣ̂* must))
(define Mε (tl Tε must))

(define/match (·simpl T₀ T₁)
  [((== ε eq?) T₁) T₁]
  [(T₀ (== ε eq?)) T₀]
  [((== T⊥ eq?) _) T⊥]
  [(_ (== T⊥ eq?)) T⊥]
  ;; Right-associate simple tcons
  [((· T₀₀ T₀₁) T₁) (·simpl T₀₀ (·simpl T₀₁ T₁))]
  ;; No simplifications
  [(T₀ T₁) (· T₀ T₁)])

(define (·simple-simpl T T′ T′simple? ρ)
  (if T′simple?
      (simple (·simpl T T′))
      (· (closed T ρ) T′)))

(define/match (¬simpl T)
  [((¬ T)) T]
  [((closed T ρ)) (closed (¬simpl T) ρ)]
  [((simple T)) (simple (¬simpl T))]
  [(T) (¬ T)])

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
    [(closed T ρ) (ν? T)]
    [_ #f])) ;; bind, event, nonevent

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

   ;; The following *p operations perform their respective derivitive operations as well as simplify

   ;; Negation differs because it waits until we have a /full/ match.
   ;; Thus, we do a nullability check to see if it is satisfied.
   ;; If a may state, we stay may only if the contract is nullable.
   ;; FIXME: Need a may fail (#f)
   (define (¬p rec T)
     (match (rec T)
       [(== M⊥ eq?) Σ*]
       [(tl T′ (== must eq?))
        (if (ν? T′)
            Mε
            (tl (¬simpl T′) must))]
       [(tl T′ t′) (tl (¬simpl T′) (if (ν? T′) may must))]
       [M (error '¬p "oops3 ~a" M)]))

   (define (·p rec T₀ T₁ T₁simple? ρ)     
     (cond
      [(ν? T₀)
       (define (·¬simpT₀T₁?simp T₀)
         (·simpl T₀ (if T₁simple? (close T₁ ρ) T₁)))
       (match (rec T₀)
         [(== M⊥ eq?) (rec T₁)] ;; Might be able to pass T₀ from nullability
         [(tl T₀′ t′)
          (match (rec T₁)
            [(== M⊥ eq?)
             (match T₀′
               [(simple T₀″)
                (tl (·simple-simpl T₀″ T₁ T₁simple? ρ) t′)]
               [T₀′ (tl (·¬simpT₀T₁?simp T₀′) t′)])]
            ;; Both derivatives matched.
            [(tl T₁′ t″)
             (define t‴ (∨ t′ t″))
             (match T₁′
               [(simple T₁′)
                (match T₀′
                  [(simple T₀″)
                   (match (·simple-simpl T₀″ T₁ T₁simple? ρ)
                     [(simple T₀″T₁)
                      (tl (simple (∪simpl (set T₀″T₁ T₁′))) t‴)]
                     [T₀″T₁ (tl (∪simpl (set (close T₁′ ρ) T₀″T₁)) t‴)])]
                  [T₀′ (tl (∪simpl (set (·¬simpT₀T₁?simp T₀′)
                                        (close T₁′ ρ)))
                           t‴)])]
               [T₁′
                (match T₀′
                  [(simple T₀″) (tl (∪simpl (set (·simple-simpl T₀″ T₁ T₁simple? ρ) T₁′)) t‴)]
                  [T₀′ (tl (∪simpl (set (·¬simpT₀T₁?simp T₀′) T₁′)) t‴)])])]
            [M (error '·p "oops4 ~a" M)])]
         [M (error '·p "oops5 ~a" M)])]
      [else
       (match (rec T₀)
         [(== M⊥ eq?) M⊥]
         [(tl (simple T′) t′) (tl (·simple-simpl T′ T₁ T₁simple? ρ) t′)]
         [(tl T′ t′) (tl (·simpl T′ T₁) t′)]
         [M (error '·p "oops6 ~a" M)])]))

   (define (close T ρ) (if (eq? ρ ρ₀) (simple T) (closed T ρ)))

   (define (klp rec T′ T Tsimple? ρ)
     (match (rec T′)
       [(== M⊥ eq?) M⊥]
       [(tl (simple T″) t′)
        (tl (·simple-simpl T″ T Tsimple? ρ) t′)]
       [(tl T″ t′) (tl (·simpl T″ T) t′)]
       [M (error 'klp "oops7 ~a" M)]))

   ;; Match some
   (define (∪p rec Ts ρ)
     (let/ec break
       (define-values (t′ Ts′ Tρs)
         (for/fold ([t must] [Ts′ ∅] [Tρs ∅]) ([T (in-set Ts)])
           (match (rec T)
             [(== Σ* eq?) (break Σ*)]
             [(== M⊥ eq?) (values t Ts′ Tρs)] ;; shortcut
             [(tl (simple T′) t′)
              (values (∨ t t′) (set-add Ts′ T′) Tρs)]
             [(tl T′ t′) (values (∨ t t′) Ts′ (set-add Tρs T′))]
             [M (error '∪p "oops8 ~a" M)])))
       (cond [(set-empty? Tρs)
              (if (set-empty? Ts′)
                  M⊥
                  (tl (simple (∪simpl Ts′)) t′))]
             [(set-empty? Ts′) (tl (∪simpl Tρs) t′)]
             [else
              (tl (∪simpl (set (close (∪simpl Ts′) ρ)
                               (∪simpl Tρs)))
                  t′)])))
   
   ;; Match all
   (define (∩p rec Ts ρ)
     (let/ec break
       (define-values (t′ Ts′ Tρs)
         (for/fold ([t must] [Ts′ ∅] [Tρs ∅]) ([T (in-set Ts)])
           (match (rec T)
             [(== M⊥ eq?) (break M⊥)]
             [(== Σ* eq?) (values t Ts′ Tρs)] ;; shortcut
             [(tl (simple T′) t′)
              (values (∧ t t′) (set-add Ts′ T′) Tρs)]
             [(tl T′ t′)
              (values (∧ t t′) Ts′ (set-add Tρs T′))]
             [M (error '∩p "oops9 ~a" M)])))
       (cond [(set-empty? Tρs)
              (if (set-empty? Ts′)
                  Σ*
                  (tl (simple (∩simpl Ts′)) t′))]
             [(set-empty? Ts′) (tl (∩simpl Tρs) t′)]
             [else
              (tl (∩simpl (set (close (∩simpl Ts′) ρ)
                               (∩simpl Tρs)))
                  t′)])))

   (define (bindp B A T ρ)
     (match (matches B A ρ)
       [#f M⊥]
       [(mres t′ ρ′) (tl (closed T ρ′) t′)]
       [M (error '∂ "oops10 ~a" M)]))
   
   (define (patp pat A ρ)
     (match (matches pat A ρ)
       [#f M⊥]
       [(mres t ρ′) (tl Tε t)]
       [M (error '∂ "oops11 ~a" M)]))
   
   (define ρ₀ #hasheq())

   ;; Top level temporal contracts with distributed ρs.
   (define (ð A T)
     (define (ð1 T) (ð A T))
     (match T
       [(== SΣ̂* eq?) Σ*]
       [(or (== ST⊥ eq?) (== Tε eq?)) M⊥]
       [(· T₀ (simple T₁)) (·p ð1 T₀ T₁ #t ρ₀)]
       [(· T₀ T₁) (·p ð1 T₀ T₁ #f ρ₀)]
       [(¬ T) (¬p ð1 T)]
       [(kl T′) (klp ð1 T′ T #f ρ₀)]
       [(∪ Ts) (∪p ð1 Ts ρ₀)]
       [(∩ Ts) (∩p ð1 Ts ρ₀)]
       [(simple T) (∂ A T ρ₀)]
       [(closed T ρ)
        (match (∂ A T ρ)
          [(? simple? T′) (closed T′ ρ)] ;; TODO: Add fvs to Tcons and restrict ρ
          [T′ T′])]
       [_ (error 'ð "Bad Tcon ~a" T)]))

   (define (∂ A T ρ)
     (define (∂1 T) (∂ A T ρ))
     (match T
       [(== Σ̂* eq?) Σ*]
       [(or (== T⊥ eq?) (== ε eq?)) M⊥]
       [(· T₀ T₁) (·p ∂1 T₀ T₁ #t ρ)]
       [(¬ T) (¬p ∂1 T)]
       [(kl T′) (klp ∂1 T′ T #t ρ)]
       [(∪ Ts) (∪p ∂1 Ts ρ)]
       [(∩ Ts) (∩p ∂1 Ts ρ)]
       ;; dseq
       [(bind B T) (bindp B A T ρ)] ;; Only introducer of ρs.
       ;; Event/unevent
       [(? event? Aor!A) (patp Aor!A A ρ)]
       [_ (error '∂ "Bad Tcon ~a" T)]))

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
