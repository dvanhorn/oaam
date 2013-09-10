#lang racket
(require racket/unit (for-syntax syntax/parse)
         racket/generic
         "ast.rkt"
         racket/stxparam
         (except-in "data.rkt" ⊥)
         (except-in "notation.rkt" ∪ ∩ set-map))
(require racket/trace)

(provide TCon-deriv^ weak-eq^ define-tcon-unit matchℓ?
         tcon? tconv?
         may must for*/δ ∨ ⊕ ∧ δ Σ̂* Σ̂*e
         ¬ · kl ε
         ¬e ·e kle εe
         constructede constructed
         call ret pcons
         $ □ Any label !pat
         $e □e Anye labele !pate
         (rename-out [∪ tor] [∩ tand] [∪e tore] [∩e tande] [bind 〈bind〉] [binde 〈binde〉])
         simple
         (struct-out tl)
         mk-Γτ
         T⊥)

(define ρ₀ #hasheq())
(struct -unmapped ()) (define unmapped (-unmapped))

(struct tcon (fvs-box label) #:transparent)
(define (tconv? x)
  (or ($? x) (□? x) (eq? x Any) (eq? x None) (!pat? x) (label? x) (constructed? x)
      (¬? x) (·? x) (kl? x) (eq? x ε) (∪? x) (∩? x) (bind? x)))
(define-simple-macro* (tcon-struct name ename (fields ...)
                                   (~optional
                                    (~or
                                     (~seq #:collect gfree*:id collect:expr)
                                     (sub-fields ...))
                                    #:defaults ([(sub-fields 1)
                                                 (syntax->list #'(fields ...))])))
  (begin 
    (struct name (fields ...) #:transparent)
    (struct ename tcon (fields ...) #:transparent
            #:methods gen:binds-variables
            [(define free-box tcon-fvs-box)
             (define/generic gfree free)
             (define (free t)
               (or (opaque-box-v (free-box t))
                   (match t
                     [(ename fvs-box label fields ...)
                      (define fvs
                       #,(cond
                          [(attribute gfree*)
                           #'(let ([gfree* gfree]) collect)]
                          [(null? (attribute sub-fields)) #'∅]
                          [else #'(set-union (gfree sub-fields) ...)]))
                      (set-opaque-box-v! fvs-box fvs)
                      fvs])))])))
;; Temporal contracts (syntactic and value)
(tcon-struct closed closede (T ρ) (T))
(define (simple T) (closed T ρ₀))
(tcon-struct ¬ ¬e (T))
(tcon-struct · ·e (T₀ T₁))
(tcon-struct kl kle (T))
(tcon-struct bind binde (B T))
(tcon-struct ∪ ∪e (Ts) #:collect free ((union-map free) Ts))
(tcon-struct ∩ ∩e (Ts) #:collect free ((union-map free) Ts))
(tcon-struct -ε -εe ())

(define ε (-ε)) (define (ε? x) (eq? x ε))
(define εe (-εe (opaque-box ∅) 0)) (define (εe? x) (eq? x εe))
(define T⊥ (∪ ∅)) (define (T⊥? x) (eq? x T⊥))
(define Σ̂* (∩ ∅)) (define (Σ̂*? x) (eq? x Σ̂*)) (define Σ̂*e (∩e (opaque-box ∅) 0 '()))
(define Tε (simple ε)) (define (Tε? x) (equal? x Tε))
(define ST⊥ (simple T⊥)) (define (ST⊥? x) (eq? x ST⊥)) ;; empty contract
(define SΣ̂* (simple Σ̂*)) (define (SΣ̂*? x) (eq? x SΣ̂*))
;; 3-valued logic
(struct -must ()) (define must (-must))
(struct -may ()) (define may (-may))
;; Top level
(struct tl (Ts t) #:transparent) ;; In this struct, Ts must all be ¬μ. t=must means no blame. t=may means blame.
(define Σ* #f) (define (set-Σ*! x) (set! Σ* x))
(define Mε-must #f) (define (set-Mε-must! x) (set! Mε-must x))
(define Mε-may #f) (define (set-Mε-may! x) (set! Mε-may x))
;; value-sets are possibly stateful and need initialization. Delay that until initialized.


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

(tcon-struct constructed constructede (c data) #:collect free ((union-map free) data))
(tcon-struct !pat !pate (pat))
(tcon-struct -Any -Anye ()) (define Any (-Any)) (define Anye (-Anye (opaque-box ∅) 0))
(tcon-struct -None -Nonee ()) (define None (-None))
(tcon-struct $ $e (x) ())
(tcon-struct □ □e (x) ())
(tcon-struct label labele (ℓ) ())

;; Niceties for writing temporal contracts using the general language of patterns.
(define (call nf pas) (constructed 'call (cons nf pas)))
(define (ret nf pv) (constructed 'ret (list nf pv)))
(define (pcons pa pd) (constructed 'cons (list pa pd)))
(define/match (event? x)
  [((constructed 'ret (list _ _))) #t]
  [((constructed 'call (list-rest _ _))) #t]
  [((!pat (? event? p))) #t]
  [(_) #f])

;; named δ since it's like Kronecker's δ
(define (δ t₀ t₁)
  (cond [(eq? t₀ 'doesnt-count) t₁]
        [(eq? t₀ t₁) t₀]
        [else may]))

(define (∧ t₀ t₁) (and t₀ t₁ (δ t₀ t₁)))

(define/match (∨ t₀ t₁)
  [(#f #f) #f]
  [((== must eq?) _) must]
  [(_ (== must eq?)) must]
  [(_ _) may])

(define/match (¬t t)
  [(#f) must]
  [((== may eq?)) may]
  [((== must eq?)) #f])

(define/match (⊕ t₀ t₁)
  [(#f #f) #f]
  [((== may eq?) _) may]
  [(_ (== may eq?)) may]
  [(_ _) must])

(define-syntax-rule (for*/δ guards body)
  (for*/fold ([res 'doesnt-count]) guards (δ res (let () body))))

;; valuations with set of possible updated bindings
(struct mres (ρs t) #:transparent)
(define ⊥ (mres ∅ #f)) (define (⊥? x) (eq? x ⊥))

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
   (define T* (·simpl T₀ T₁))
   (unless (open? T*) (error '·simpl "Introduced closed (· ~a ~a) → ~a" T₀ T₁ T*))
   (closed T* ρ₀)]
  ;; Right-associate simple tcons
  [((· T₀₀ T₀₁) T₁) (·simpl T₀₀ (·simpl T₀₁ T₁))]
  ;; No simplifications
  [(T₀ T₁) (· T₀ T₁)])

(define/match (klsimpl T)
  [((or (? ε?) (? T⊥?))) ε]
  [((or (? Tε?) (? ST⊥?))) Tε]
  [((kl T)) (klsimpl T)]
  [((? Σ̂*?)) Σ̂*]
  [((? SΣ̂*?)) SΣ̂*]
  [((closed T ρ))
   (define T* (klsimpl T))
   (closed T* ρ)] ;; TODO: restrict bindings
  [(T) (kl T)])

(define/match (¬simpl T)
  [((¬ T)) T]
  [((closed T ρ))
   (define T* (¬simpl T))
   (closed T* ρ)]
  [(T) (¬ T)])

;; Flatten ∪s and ∩s into one big ∪ or ∩.
;; All closed Ts with the same environment are collated.
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
    (define T* (f Ts))
    (unless (open? T*) (error 'close-hash "Introduced closed ~a → ~a" Ts T*))
    (closed T* ρ)))

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
(define ∪simpl (∪∩-simpl T⊥ T⊥? Σ̂* Σ̂*? ∪ ∪? ∪-Ts))
(define ∩simpl (∪∩-simpl Σ̂* Σ̂*? T⊥ T⊥? ∩ ∩? ∩-Ts))

;; Combine bindings giving preference to the right hash.
(define (◃ ρ₀ ρ₁)
  (for/fold ([ρ ρ₀]) ([(k v) (in-hash ρ₁)])
    (hash-set ρ k v)))

(define (⋈ ρs₀ ρs₁)
  (for*/set ([ρ (in-set ρs₀)]
             [ρ′ (in-set ρs₁)])
    (ρ . ◃ . ρ′)))

;; Match every pattern in S via f
(define (⨅ S f)
  (let/ec break
    (define-values (ρs t)
      (for/fold ([ρs (set #hasheq())]
                 [t must])
          ([s (in-set S)])
        (match (f s)
          [(mres ρs′ t′)
           (if t′
               (values (ρs . ⋈ . ρs′) (∧ t t′))
               (break ⊥))]
          [err (error '⨅ "Bad res ~a" err)])))
    (mres ρs t)))

;; Match patterns in L with corresponding values in R via f.
(define (⨅/lst f L R)
  (let matchlst ([L L] [R R] [t must] [ρs (set #hasheq())])
    (match* (L R)
      [('() '()) (mres ρs t)]
      [((cons l L) (cons r R))
       (match (f l r)
         [(mres ρs′ t′)
          (if t′
              (matchlst L R (∧ t t′) (ρs . ⋈ . ρs′))
              ⊥)]
         [err (error '⨅ "Bad res ~a" err)])]
      [(_ _) ⊥])))

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

(define (open? T)
  (match T
    [(· T₀ T₁) (and (open? T₀) (open? T₁))]
    [(or (∪ Ts) (∩ Ts)) (for/and ([T (in-set Ts)]) (open? T))]
    [(or (¬ T) (kl T) (bind _ T)) (open? T)]
    [(closed T ρ) #f]
    [_ #t]))

(define-syntax-parameter matchℓ? #f)
(define-signature weak-eq^ (≃ σgetter))
(define-signature TCon-deriv^ (ð))

(define-syntax-rule (Δ-like C acc-nothing pat ⊔ in-collection bad? bad op)
  (let ()
    (define-values (Ts t)
      (for/fold ([Ts acc-nothing] [t 'doesnt-count]) ([M (in-collection C)])
        (match-define (pat Ts* t*) (op M))
        (values (⊔ Ts Ts*) (δ t t*))))
    (if (bad? Ts)
        bad
        (pat Ts t))))

(define-simple-macro* (mk-Γτ name)
  (define (name reachable touches τ)
    ;; References to variables in ρkill get rewritten to None
    ;; Any bindings we come across that shadow names in ρkill get removed.
    ;; Constructed data containing None becomes None.
    ;; Negated matching on constructed data containing None becomes Any.
    (define (Γpattern ρkill event)
      (let build ([event event] [ρnew ρkill])
        (define (build/l pats)
          (let/ec found-none
            (let loop ([pats pats] [ρnew* ρnew])
              (match pats
                ['() (values ρnew* '())]
                [(cons pat pats)
                 (define-values (ρnew** pat*) (build pat ρnew*))
                 (cond [(eq? pat* None) (found-none ρnew None)]
                       [else
                        (define-values (ρnew*** pats*) (loop pats ρnew**))
                        (values ρnew*** (cons pat* pats*))])]))))
        (match event
          [(constructed kind pats)
           (define-values (ρnew* pats*) (build/l pats))
           (if (eq? pats* None)
               (values ρnew None)
               (values ρnew* (constructed kind pats*)))]
          [(!pat pat)
           (define-values (drop pat*) (build pat ρnew))
           (values ρnew
                   (cond [(eq? pat* None) Any]
                         [(eq? pat* Any) None]
                         [else (!pat pat*)]))]
          [($ x) (values ρnew (if (hash-has-key? ρkill x) None event))]
          [(□ x) (values (hash-remove ρnew x) event)]
          [(or (? label?) (== Any eq?) (== None eq?)) (values ρnew event)]
          [(? value-set? vs)
           (values ρnew
                   (for*/value-set ([v (in-value-set vs)]
                                    [v* (in-value (let-values ([(drop v*) (build v ρnew)]) v*))]
                                    #:unless (eq? v* None))
                                   v*))]
          [v (if (subset? (touches v) reachable)
                 (values ρnew v)
                 (values ρnew None))])))
    (define (remove-unreachable ρ)
      ;; Bindings that refer to nothing are removed so that has-key? is
      ;; sufficient to change references into None
      (for/fold ([ρ* #hasheq()]
                 [ρkill #hasheq()])
          ([(x vs) (in-hash ρ)])
        (define vs*
          (for/fold ([vs* nothing])
              ([v (in-value-set vs)]
               #:when (subset? (touches v) reachable))
            (⊓1 vs* v)))
        (if (nothing? vs*)
            (values ρ* (hash-set ρkill x #t))
            (values (hash-set ρ* x vs*) ρkill))))
    (for/σ ([(η Ts) (in-σ τ)]
            #:when (η . ∈ . reachable))
           (values
            η
            #,(if (syntax-parameter-value #'Γτ?)
                  #'(for/value-set ([T (in-value-set Ts)])
                                   (define start-T T)
                                   (let Γsimpl* ([T T] [ρkill #hasheq()])
                                        (define (Γsimpl T) (Γsimpl* T ρkill))
                                        (match T
                                          [(∪ Ts) (∪simpl (for/set ([T (in-set Ts)]) (Γsimpl T)))]
                                          [(∩ Ts) (∩simpl (for/set ([T (in-set Ts)]) (Γsimpl T)))]
                                          [(¬ T) (¬simpl (Γsimpl T))]
                                          [(kl T) (klsimpl (Γsimpl T))]
                                          [(· T₀ T₁) (·simpl (Γsimpl T₀) (Γsimpl T₁))]
                                          [(bind B T)
                                           (define-values (ρkill* B*) (Γpattern ρkill B))
                                           (cond [(eq? B* None) T⊥]
                                                 [else
                                                  (define T* (Γsimpl* T ρkill*))
                                                  (cond [(eq? T* T⊥) (¬simpl B*)]
                                                        [else (bind B* T*)])])]
                                          [(closed T ρ)
                                           ;; ρkill gets created here and only made smaller.
                                           (define-values (ρ* ρkill*) (remove-unreachable ρ))
                                           (define T* (Γsimpl* T ρkill*))
                                           (cond [(eq? T* T⊥) ST⊥]
                                                 [(eq? T* Σ̂*) SΣ̂*]
                                                 [else (closed T* ρ*)])]
                                          [(? ε?) ε]
                                          [_ (define-values (ρkill* A) (Γpattern ρkill T))
                                             (match A
                                               [(== None eq?) T⊥]
                                               [(== Any eq?) Σ̂*]
                                               [_ A])])))
                  #'Ts)))))

(define-syntax-rule (define-tcon-unit name init)
  (begin
    (define (init)
      (set-Σ*! (tl (singleton SΣ̂*) must))
      (set-Mε-must! (tl (singleton Tε) must))
      (set-Mε-may! (tl (singleton Tε) may)))

    (define M⊥ (tl nothing #f)) (define (M⊥? x) (eq? x M⊥))
    ;; The following *p operations perform their respective derivitive operations as well as simplify
    (define (Δ lst)
      (Δ-like lst nothing tl ⊓ in-list nothing? M⊥ values))
    ;; Negation differs because it waits until we have a /full/ match.
    ;; Thus, we do a nullability check to see if it is satisfied.
    ;; If a may state, we stay may only if the contract is nullable.
    (define (¬p T)
      (match T
        [(? M⊥?) Σ*]
        [(tl Ts′ t)
         (define Ts″
           (let/ec break
             (for/fold ([acc nothing]) ([T′ (in-value-set Ts′)])
               (if (ν? T′)
                   (break nothing)
                   (⊓1 acc (¬simpl T′))))))
         (if (nothing? Ts″) M⊥ (tl Ts″ t))]
        [M (error '¬p "oops3 ~a" M)]))

    ;; ð_A (· T₀ T₁) = ð_A T₀ + ν(T₀)·ð_A T₁
    ;; ∂_A (· T₀ T₁) ρ = ∂_A T₀,ρ + ν(T₀)·∂_A T₁,ρ
    (define (·p νT₀ ∂T₀ ∂T₁-promise T₁)
      (define-values (lefts t)
        (match ∂T₀
          [(? M⊥?) (values nothing #t)]
          [(tl Ts′ t′) (values (for/value-set ([T′ (in-value-set Ts′)]) (·simpl T′ T₁)) t′)]
          [M (error '·p "oops6 ~a" M)]))
      (cond
       [νT₀
        (match (force ∂T₁-promise)
          [(? M⊥?) (if (nothing? lefts)
                       M⊥
                       (tl lefts t))]
          ;; Both derivatives matched.
          [(and right (tl T₁s′ t′))
           (if (nothing? lefts)
               right
               (tl (for*/value-set ([left (in-value-set lefts)]
                                    [T₁′ (in-value-set T₁s′)])
                                   (∪simpl (set left T₁′)))
                   (δ t t′)))]
          [M (error '·p "oops4 ~a" M)])]
       [(nothing? lefts) M⊥]
       [else (tl lefts t)]))
    #;(trace ·p)

    (define (klp M T)
      (match M
        [(? M⊥?) M⊥]
        [(tl Ts″ t′) (tl (for/value-set ([T″ (in-value-set Ts″)]) (·simpl T″ T)) t′)]
        [M (error 'klp "oops7 ~a" M)]))

    ;; Forms a cross-product of all Ms' Ts.
    (define ((∪∩p ⊥ bin simpl) Ms)
      (define-values (Tss′ t′)
        (for/fold ([acc ∅] [t 'doesnt-count]) ([M (in-set Ms)])
          (match M
            [(tl Ts′ t′) (values (set-add acc Ts′) (δ t t′))])))
      (tl (for/value-set ([Ts′ (in-set (set-of-sets-Π Tss′))]) (simpl Ts′)) t′))
   
    ;; S is a set of value-sets. We return a set of sets.
    (define (set-of-sets-Π S)
      (cond
       [(∅? S) (set ∅)]
       [else (define A (set-first S))
             (define S* (set-rest S))
             (for*/set ([a (in-value-set A)]
                        [tail (in-set (set-of-sets-Π S*))])
               (set-add tail a))]))

    (define ∪p (∪∩p #f ∨ ∪simpl))
    (define ∩p (∪∩p must ∧ ∩simpl))
    
    (define-unit name
      (import weak-eq^)
      (export TCon-deriv^)
      (define (force* v)
        (match v
          [(addr a) (σgetter a)]
          [(? value-set?) v]
          [else (singleton v)]))

      (define (matches P A γ)
        (define (matches1 P) (matches P A γ))
        (define (matches2 P A) (matches P A γ))
        (match P
          [(and (? generic-set?) (not (? list?))) (⨅ P matches1)]
          [(!pat pat)
           (match-define (mres _ t) (matches1 pat))
           (if (eq? must t)
               ⊥
               (mres (set γ) (¬t t)))]
          [(constructed kind pats)
           (match A
             [(constructed (== kind eq?) data)
              (⨅/lst matches2 pats data)]
             ;; constructed, but also data
             [(consv a d) ;; INVARIANT: pats ≡ (list pata patd)
              (cond
               [(eq? kind 'cons) (⨅/lst matches2 pats (list (σgetter a) (σgetter d)))]
               [else ⊥])]
             [(addr a) (matches2 P (σgetter a))]
             [(? value-set?)
              (define-syntax-rule (op v) (matches2 P v))
              (Δ-like A ∅ mres set-union in-value-set ∅? ⊥ op)]
             [(or (? vectorv?) (? vectorv-immutable?) (? vectorv^?) (? vectorv-immutable^?))
              (error 'todo "Match on vectors")]
             [_ ⊥])]
          [(== Any eq?) (mres (set γ) must)]
          [(== None eq?) ⊥]
          [(label ℓ)
           (if (matchℓ? A ℓ)
               (mres (set γ) must)
               ⊥)]
          [(□ x) (mres (set (hash-set γ x A)) must)]
          [($ x)
           (match (hash-ref γ x unmapped)
             [(== unmapped eq?) ⊥]
             [v (matches2 v A)])]
          [v
           (define v* (force* v))
           (define A* (force* A))
           (define t
             (for*/δ ([v (in-value-set v*)]
                      [v′ (in-value-set A*)])
                     (≃ v v′)))
           (if t
               (mres (set γ) t)
               ⊥)]))

      (define (bindp B A T ρ)
        (match (matches B A ρ)
          [(mres ρs′ t′)
           (cond [t′
                  (tl (for/value-set ([ρ′ (in-set ρs′)])
                                     (closed T ρ′))
                      t′)]
                 [else M⊥])]))

      (define (patp pat A ρ)
        (match (matches pat A ρ)
          [(mres ρs′ (== must eq?)) Mε-must]
          [(mres ρs′ (== may eq?)) Mε-may]
          [_ M⊥]))

      ;; Top level temporal contracts with distributed ρs.
      ;; Returns a (mres Set[TCon] valuation)
      (define (ð* A T)
        (let ð ([T T])
             #;(trace ð)
             (match T
               [(? SΣ̂*?) Σ*]
               [(or (? ST⊥?) (? Tε?)) M⊥]
               [(· T₀ T₁) (·p (ν? T₀) (ð T₀) (delay (ð T₁)) T₁)]
               [(¬ T) (¬p (ð T))]
               [(kl T′) (klp (ð T′) T)]
               ;; Instead of performing a cross-product, just output the set of possibilities.
               [(∪ Ts) (∪p (for/set ([T (in-set Ts)]) (ð T)))
                #;(Δ (set-map Ts ð))
                ]
               [(∩ Ts) (∩p (for/set ([T (in-set Ts)]) (ð T)))]
               [(closed T ρ) (∂ A T ρ)] ;; TODO: Add fvs to Tcons and restrict ρ
               [A* (∂ A A* ρ₀)]
               [_ (error 'ð "Bad Tcon ~a" T)])))
      #;(trace ð*)
      (define ð ð*)

      ;; Treat T as if each component of T is closed by ρ (down to bind)
      (define (∂ A T ρ)
        (let ∂ ([T T])
          #;(trace ∂)
          (unless (open? T) (error '∂ "Bad T ~a" T))
          (match T
            [(? Σ̂*?) Σ*]
            [(or (? T⊥?) (? ε?)) M⊥]
            [(· T₀ T₁) (·p (ν? T₀) (∂ T₀) (delay (∂ T₁)) (closed T₁ ρ))]
            [(¬ T) (¬p (∂ T))]
            [(kl T′) (klp (∂ T′) T)]
            [(∪ Ts) (∪p (for/set ([T (in-set Ts)]) (∂ T)))
             #;(Δ (set-map Ts ∂))
             ]
            [(∩ Ts) (∩p (for/set ([T (in-set Ts)]) (∂ T)))]
            ;; dseq
            [(bind B T) (bindp B A T ρ)] ;; Only introducer of ρs.
            ;; Event/unevent
            [(? event? Aor!A) (patp Aor!A A ρ)]
            [_ (error '∂ "Bad Tcon ~a" T)])))
      #;(trace ∂)
      )))

