#lang racket
(require racket/unit 
         "ast.rkt"
         (except-in "notation.rkt" ∪ ∩))
(require racket/trace)

(provide TCon-deriv^ TCon-deriv@ weak-eq^
         may must for/∧ for*/∧ ⊕
         ¬ · kl bind ε
         call ret !call !ret
         $ □ Any label
         (rename-out [∪ tor] [∩ tand])
         simple
         (struct-out tl)         
         M⊥)

(define ρ₀ #hasheq())
(struct -unmapped ()) (define unmapped (-unmapped))

(define (default-free-box e) (error 'free-box "Tcons don't have fvs, so no box ~a" e))
(define-simple-macro* (tcon-struct name (fields ...))
  (struct name (fields ...) #:transparent 
         ;; #:methods #,(syntax-local-introduce #'gen:binds-variables)
          ;;[(define free-box default-free-box)]
          ))
;; Temporal contracts
(tcon-struct closed (T ρ))
(define (simple T) (closed T ρ₀))
(tcon-struct ¬ (T))
(tcon-struct · (T₀ T₁))
(tcon-struct kl (T))
(tcon-struct bind (B T))
(tcon-struct ∪ (Ts))
(tcon-struct ∩ (Ts))
(tcon-struct -ε ())

(define ε (-ε)) (define (ε? x) (eq? x ε))
(define T⊥ (∪ ∅)) (define (T⊥? x) (eq? x T⊥))
(define Σ̂* (∩ ∅)) (define (Σ̂*? x) (eq? x Σ̂*))
(define Tε (simple ε)) (define (Tε? x) (equal? x Tε))
(define ST⊥ (simple T⊥)) (define (ST⊥? x) (eq? x ST⊥)) ;; empty contract
(define SΣ̂* (simple Σ̂*)) (define (SΣ̂*? x) (eq? x SΣ̂*))
;; 3-valued logic
(struct -must ()) (define must (-must))
(struct -may ()) (define may (-may))
;; Top level
(struct tl (T t) #:transparent)
(define M⊥ (tl ST⊥ must)) (define (M⊥? x) (eq? x M⊥))
(define Σ* (tl SΣ̂* must)) (define (Σ*? x) (eq? x Σ*))
(define Mε (tl Tε must)) (define (Mε? x) (eq? x Mε))

(define (∂? x)
  (or (¬? x) (·? x) (event? x) (kl? x) (bind? x) (∪? x) (∩? x) (ε? x)))
(define (ð? x)
  (match x
    [(or (closed (? ∂?) (? hash?))
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
(define (ret nf pv) (constructed 'ret (list nf pv)))
(define (!call nf pas) (!constructed 'call (cons nf pas)))
(define (!ret nf pv) (!constructed 'ret (list nf pv)))
(define/match (event? x)
  [((constructed 'ret (list _ _))) #t]
  [((!constructed 'ret (list _ _))) #t]
  [((constructed 'call (list-rest _ _))) #t]
  [((!constructed 'call (list-rest _ _))) #t]
  [(_) #f])

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

(define/match (⊕ t₀ t₁)
  [(#f #f) #f]
  [((== may eq?) _) may]
  [(_ (== may eq?)) may]
  [(_ _) must])

(define-syntax-rule (for/∧ guards body)
  (for/fold ([res must]) guards (∧ res (let () body))))
(define-syntax-rule (for*/∧ guards body)
  (for*/fold ([res must]) guards (∧ res (let () body))))

;; valuations with updated bindings
(struct mres (t ρ) #:transparent)

(define/match (·simpl T₀ T₁)
  [((? ε?) T₁) T₁]
  [(T₀ (? ε?)) T₀]
  [((? Tε?) T₁) T₁]
  [(T₀ (? Tε?)) T₀]
  [((? T⊥?) _) T⊥]
  [(_ (? T⊥?)) T⊥]
  [((? ST⊥?) _) T⊥]
  [(_ (? ST⊥?)) T⊥]
  [((closed T₀ ρ₀) (closed T₁ (== ρ₀ eq?)))
   (closed (·simpl T₀ T₁) ρ₀)]
  ;; Right-associate simple tcons
  [((· T₀₀ T₀₁) T₁) (·simpl T₀₀ (·simpl T₀₁ T₁))]
  ;; No simplifications
  [(T₀ T₁) (· T₀ T₁)])

(define/match (¬simpl T)
  [((¬ T)) T]
  [((closed T ρ)) (closed (¬simpl T) ρ)]
  [(T) (¬ T)])

;; Flatten ∪s and ∪s into one (or two) big ∪ or ∩. simple and not.
(define (flat-collect pred extract ⊥? ⊤? Ts)
  (let/ec found⊤
    (define-values (sTs Tρs)
      (let recur ([Ts Ts] [simples (hasheq)] [a ∅] [Tρ #f])
        (for/fold ([simples simples] [a a]) ([T (in-set Ts)])
          (define (do T ρ)
            (match T
              [(? ⊤? T) (found⊤ #t #f #f)]
              [(? ⊥? T) (values simples a)]
              [(? pred T)
               (recur (extract T) simples a ρ)]
              [(closed T ρ) (do T ρ)]
              [else (if ρ
                        (values (hash-add simples ρ T) a)
                        (values simples (set-add a T)))]))
          (do T Tρ))))
    (values #f sTs Tρs)))
(define (close-hash f h)
  (for/set ([(ρ Ts) (in-hash h)])
    (closed (f Ts) ρ)))

(define ((simpled b f) sTs)
  (cond
   [(set-empty? sTs) b]
   [(= (set-count sTs) 1) (set-first sTs)]
   [else (f sTs)]))
;; If Ts inside a closed, this won't close it.
(define ((∪∩-simpl s⊥ ⊥? ⊤ ⊤? ∪∩ ∪∩? ∪∩-Ts) Ts)
  (define-values (found⊤? sTs Tρs) (flat-collect ∪∩? ∪∩-Ts ⊥? ⊤? Ts))
  (define ∪∩s (simpled s⊥ ∪∩))
  (cond [found⊤? ⊤]
        [(set-empty? Tρs) (∪∩s (close-hash ∪∩s sTs))]
        [(eq? 0 (hash-count sTs)) (∪∩s Tρs)]
        [else (∪∩ (set-union Tρs (close-hash ∪∩s sTs)))]))
(define ∪simpl (∪∩-simpl ST⊥ T⊥? Σ̂* Σ̂*? ∪ ∪? ∪-Ts))
(define ∩simpl (∪∩-simpl SΣ̂* Σ̂*? T⊥ T⊥? ∩ ∩? ∩-Ts))

;; Combine bindings giving preference to the right hash.
(define (◃ ρ₀ ρ₁)
  (for/fold ([ρ ρ₀]) ([(k v) (in-hash ρ₁)])
    (hash-set ρ k v)))

;; Match every pattern in S via f
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

;; Match patterns in L with corresponding values in R via f.
(define (⨅/lst f L R)
  (let matchlst ([L L] [R R] [t must] [ρ #hasheq()])
    (match* (L R)
      [('() '()) (mres t ρ)]
      [((cons l L) (cons r R))
       (match (f l r)
         [#f #f]
         [(mres t′ ρ′) (matchlst L R (∧ t t′) (ρ . ◃ . ρ′))]
         [err (error '⨅ "Bad res ~a" err)])]
      [(_ _) #f])))

;; Is the contract nullable?
(define (ν? T)
  (match T
    [(or (kl _) (? ε?)) #t]
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
      [v (define t
           (cond [(set? A)
                  (for/fold ([t #f]) ([v′ (in-set A)])
                    (⊕ (≃ v v′) t))]
                 [else (≃ v A)]))
         (and t (mres t γ))]))
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
   (define (¬p T)
     (match T
       [(? M⊥?) Σ*]
       [(tl T′ (== must eq?))
        (if (ν? T′)
            (begin
              (printf "Failing state!~%")
              M⊥)
            (tl (¬simpl T′) must))]
       [(tl T′ t′) (tl (¬simpl T′) (if (ν? T′)
                                       (begin 
                                         (printf "May fail state!~%")
                                         may)
                                       (begin
                                         (printf "Not nullable, even though matched~%")
                                         must)))]
       [M (error '¬p "oops3 ~a" M)]))

   ;; ð_A (· T₀ T₁) = ð_A T₀ + ν(T₀)·ð_A T₁
   ;; ∂_A (· T₀ T₁) ρ = ∂_A T₀,ρ + ν(T₀)·∂_A T₁,ρ
   (define (·p νT₀ ∂T₀ ∂T₁-promise T₁ bin)     
     (define-values (left t)
       (match ∂T₀
         [(? M⊥?) (values ST⊥ must)]
         [(tl T′ t′) (values (·simpl T′ T₁) t′)]
         [M (error '·p "oops6 ~a" M)]))
     (cond
      [νT₀
       (match (force ∂T₁-promise)
         [(? M⊥?) (tl left t)]
         ;; Both derivatives matched.
         [(tl T₁′ t′) (tl (∪simpl (set left T₁′)) (bin t t′))]
         [M (error '·p "oops4 ~a" M)])]
      [else (tl left t)]))

   (define (klp T′ T)
     (match T′
       [(? M⊥?) M⊥]
       [(tl T″ t′) (tl (·simpl T″ T) t′)]
       [M (error 'klp "oops7 ~a" M)]))

   (define ((∪∩p ⊥ bin simpl) Ts)
     (define-values (Ts′ t′)
      (for/fold ([acc ∅] [t ⊥]) ([T (in-set Ts)])
        (match T
          [(tl T′ t′) (values (set-add acc T′) (bin t t′))])))
     (tl (simpl Ts′) t′))

   (define ∪p+ (∪∩p #f ∨ ∪simpl))
   (define ∪p- (∪∩p #f ⊕ ∪simpl))
   (define ∩p (∪∩p must ∧ ∩simpl))

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
 
   ;; Top level temporal contracts with distributed ρs.
   (define (ð* A T)
     (let ð± ([T T] [± #t])
       (define (ð1 T) (ð± T ±))
       (define-values (u v) (if ± (values ∪p+ ∨) (values ∪p- ⊕)))
       (match T
         [(? SΣ̂*?) Σ*]
         [(or (? ST⊥?) (? Tε?)) M⊥]
         [(· T₀ T₁) (·p (ν? T₀) (ð1 T₀) (delay (ð1 T₁)) T₁ v)]
         [(¬ T) (¬p (ð± T (not ±)))]
         [(kl T′) (klp (ð1 T′) T)]
         [(∪ Ts) (u (set-map ð1 Ts))]
         [(∩ Ts) (∩p (set-map ð1 Ts))]
         [(closed T ρ) (∂ A T ρ ±)] ;; TODO: Add fvs to Tcons and restrict ρ
         [_ (error 'ð "Bad Tcon ~a" T)])))
   (define ð ð*)
 
   ;; Treat T as if each component of T is closed by ρ (down to bind)
   (define (∂ A T ρ ±)
     (define (∂1 T) (∂ A T ρ ±))
     (define (∂± T ±) (∂ A T ρ ±))
     (define-values (u v) (if ± (values ∪p+ ∨) (values ∪p- ⊕)))
     (match T
       [(? Σ̂*?) Σ*]
       [(or (? T⊥?) (? ε?)) M⊥]
       [(· T₀ T₁) (·p (ν? T₀) (∂1 T₀) (delay (∂1 T₁)) (closed T₁ ρ) v)]
       [(¬ T) (¬p (∂± T (not ±)))]
       [(kl T′) (klp (∂1 T′) (closed T ρ))]
       [(∪ Ts) (u (set-map ∂1 Ts))]
       [(∩ Ts) (∩p (set-map ∂1 Ts))]
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
          [(? M⊥?) M⊥]
          [M (error 'run* "oops12 ~a" M)])]
       [err (error 'run* "Bad ~a" err)]))
   (define run run*))

(define-unit concrete@
  (import)
   (export weak-eq^)
   (define (≃ x y) (and (equal? x y) must))
   (define matchℓ? eq?))

(define-values/invoke-unit/infer (export TCon-deriv^) (link concrete@ TCon-deriv@))
