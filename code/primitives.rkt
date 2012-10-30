#lang racket

(require "data.rkt" "notation.rkt" "do.rkt"
         "primitive-maker.rkt"
         (for-syntax syntax/parse) ;; for core syntax-classes
         racket/unsafe/ops)
(provide primitive? changes-store? reads-store? primitive? prim-constants
         mk-prims hash->kind
         ;; reprovide
         snull yield force getter widen delay)

;; Classify different hash literals
(define (hash->kind h)
  (cond [(immutable? h)
         (cond [(hash-equal? h) 'immutable-equal]
               [(hash-eqv? h) 'immutable-eqv]
               [(hash-eq? h) 'immutable-eq])]
        [else
         (cond [(hash-equal? h) 'mutable-equal]
               [(hash-eqv? h) 'mutable-eqv]
               [(hash-eq? h) 'mutable-eq])]))

(define (immutable-hash? h)
  (case (hashv-kind h) [(immutable-equal immutable-eqv immutable-eq) #t] [else #f]))

(define-simple-macro* (define/read (name:id rσ:id v:id ...) body ...+)
  ;; XXX: not capture-avoiding, so we have to be careful in our definitions
  (define-simple-macro* (name rσ vs)
    (match vs
      [(list v ...) body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

(define-simple-macro* (define/basic (name:id v:id ...) body ...+)
  (define-simple-macro* (name vs)
    (match vs
      [(list v ...) body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

(define-simple-macro* (define/write (name:id rσ:id l:id δ:id v:id ... [opv:id opval:expr] ...) body ...+)
  (define-simple-macro* (name rσ l δ vs)
    (match vs
      [(list-rest v ... rest)
       #,@(let ([defvs (length (syntax->list #'(opval ...)))])
            (if (zero? defvs)
                #'()
                #`((define rest-len (length rest))
                   (define rest* (for/vector #:length #,defvs
                                             ([v* (in-list rest)]) v*))
                   ;; Populate the rest of the default arguments with w
                   (for ([v* (in-list (drop (list opval ...) rest-len))]
                         [i (in-naturals rest-len)])
                     (unsafe-vector-set! rest* i v*))
                   (define-values (opv ...)
                     (values #,@(for/list ([i (in-range defvs)])
                                  #`(unsafe-vector-ref rest* #,i)))))))
       body ...]
      [_ (error 'name "internal error: Bad input ~a" vs)])))

;; XXX: Unfortunately needs σ
(define-simple-macro* (yield-both bσ)
  (do (bσ) ([b (in-list '(#t #f))]) (yield b)))

(define-for-syntax (prim-defines clos? rlos?)
  (with-syntax ([clos? clos?]
                [rlos? rlos?])
    #'((define-syntax-rule (yield-delay ydσ v)
         (do (ydσ) ([v* (delay ydσ v)]) (yield v*)))
       (define-simple-macro* (errorv vs)
         (begin (log-info "Error reachable ~a" vs)
                ;; Really this should be continue, but graphs.sch uses
                ;; with-input-from-file, which Suresh cheated on.
                (yield (void))
                #;
                (continue)))

       (define/basic (quotientv z0 z1)
         (cond [(or (number^? z0) (number^? z1))
                (yield number^)]
               [(zero? z1)
                (log-info "Quotient undefined on 0")
                (continue)]
               [else (yield (widen (quotient z0 z1)))]))

       (define/basic (modulov z0 z1)
         (cond [(or (number^? z0) (number^? z1))
                (yield number^)]
               [(zero? z1)
                (log-info "Modulo undefined on 0")
                (continue)]
               [else (yield (widen (quotient z0 z1)))]))

       (define/basic (remainderv z0 z1)
         (cond [(or (number^? z0) (number^? z1))
                (yield number^)]
               [(zero? z1)
                (log-info "Remainder undefined on 0")
                (continue)]
               [else (yield (widen (remainder z0 z1)))]))

       (define/basic (procedure?v v) (yield (or (clos? v) (rlos? v))))
       (define/basic (vectorv-length v)
         (match v
           [(or (vectorv len _) (vectorv^ len _)
                (vectorv-immutable len _)) (yield len)]
           [(or (? vector^?) (? vector-immutable^?)) (yield number^)]
           [_ (vector-length v)]))

       (define/basic (integer->charv z)
         (cond [(number^? z) (yield char^)]
               [(integer? z) (yield (widen (integer->char z)))]
               [else
                (log-info "integer->charv on non-integer")
                (continue)]))

       (define/basic (hashv-equal? h)
         (case (hashv-kind h) [(immutable-equal mutable-equal) #t] [else #f]))
       (define/basic (hashv-eqv? h)
         (case (hashv-kind h) [(immutable-eqv mutable-eqv) #t] [else #f]))
       (define/basic (hashv-eq? h)
         (case (hashv-kind h) [(immutable-eq mutable-eq) #t] [else #f]))
       ;; Not a general predicate. Only for immutable hashes, vectors, strings, byte-strings and boxes.
       ;; Currently we have only immutable hashes.
       (define/basic (immutablev? v)
         (match v
           [(? hashv? h) (yield (immutable-hash? h))]
           [(or (? vectorv-immutable^?)
                (? vector-immutable^?)
                (? immutable? (? vector?)))
            (yield #t)]
           [_ (yield #f)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that read the store

       ;; TODO: add blackhole data and immutable vectors
       (define/read (equalv? eσ v0 v1)
         (define-syntax-rule (both-if pred) (if pred (yield-both eσ) (yield #f)))
         (do (eσ) ([v0 (force eσ v0)]
                   [v1 (force eσ v1)])
           (match* (v0 v1)
             [((== ●) _) (yield-both eσ)]
             [(_ (== ●)) (yield-both eσ)]
             [((? clos?) _) (both-if (clos? v1))]
             [(_ (? clos?)) (yield #f)] ;; first not a closure
             [((? rlos?) _) (both-if (rlos? v1))]
             [(_ (? rlos?)) (yield #f)]
             [((or (== cons^) (? consv?)) _)
              (both-if (or (consv? v1) (eq? v cons^)))] ;; FIXME: overapproximate for concrete
             [(_ (or (== cons^) (? consv?))) (yield #f)] ;; first not a cons
             [((or (== vector^) (== vector-immutable^)
                   (? vector?) ;; Racket's immutable vectors
                   (? vectorv-immutable^?) (? vectorv?)
                   (? vectorv^?) (? vectorv-immutable?)) _)
              (both-if (or (vectorv? v1) (vectorv-immutable? v1) (eq? v1 vector^)
                           (eq? v1 vector-immutable^)
                           (vector? v1)
                           (vectorv-immutable^? v1)))] ;; FIXME: not right for concrete
             [(_ (or (== vector^) (== vector-immutable^)
                     (? vectorv-immutable^?) (? vectorv?)
                     (? vectorv^?) (? vectorv-immutable?)
                     (? vector?)))
              (yield #f)] ;; first not a vector
             [((? primop?) _) (yield (equal? v0 v1))]
             [(_ (? primop?)) (yield #f)] ;; first not a primop
             [((? number?) _) (cond [(number^? v1) (yield-both eσ)]
                                    [(number? v1) (yield (= v0 v1))]
                                    [else (yield #f)])]
             [((? number^?) _) (both-if (or (number^? v1) (number? v1)))]
             [(_ (? number^?)) (yield #f)]
             [((? string?) _) (cond [(eq? string^ v1) (yield-both eσ)]
                                    [(string? v1) (yield (string=? v0 v1))]
                                    [else (yield #f)])]
             [((== string^) _) (both-if (or (eq? string^ v1) (string? v1)))]
             [((? char?) _) (cond [(eq? char^ v1) (yield-both eσ)]
                                  [(char? v1) (yield (char=? v0 v1))]
                                  [else (yield #f)])]
             [((== char^) _) (both-if (or (eq? char^ v1) (char? v1)))]
             [(_ (== string^)) (yield #f)]
             [((? symbol?) _) (cond [(eq? symbol^ v1) (yield-both eσ)]
                                    [(symbol? v1) (yield (eq? v0 v1))]
                                    [else (yield #f)])]
             [((== symbol^) _) (both-if (or (eq? symbol^ v1) (symbol? v1)))]
             [(_ (or (? symbol?) (== symbol^))) (yield #f)]
             [((? boolean?) _) (yield (equal? v0 v1))]
             [('() _) (yield (eq? '() v1))]
             [(_ '()) (yield #f)]
             [((? void?) _) (yield (void? v1))]
             [(_ (? void?)) (yield #f)]
             [((? input-port^?) _) (both-if (input-port^?))]
             [(_ (? input-port^?)) (yield #f)]
             [((? output-port^?) _) (both-if (output-port^?))]
             [(_ (? output-port^?)) (yield #f)]
             [((? input-port?) _) (equal? v0 v1)]
             [(_ (? input-port?)) (yield #f)]
             [((? output-port?) _) (equal? v0 v1)]
             [(_ (? output-port?)) (yield #f)]
             [(_ (== eof)) (yield (eof-object? v0))]
             [((== eof) _) (yield (eof-object? v1))]
             [(_ _) (error 'equalv? "Incomplete match ~a ~a" v0 v1)])))

       (define/read (vectorv-ref vrσ vec z)
         (match vec
           [(vectorv _ l)
            (cond [(number^? z)
                   (error 'vectorv-ref "Abstract vectors should have a single cell")]
                  [(or (< z 0) (>= z (length l)))
                   (log-info "vectorv-ref out of bounds")
                   (continue)]
                  [else (yield-delay vrσ (list-ref l z))])]
           [(or (vectorv^ _ abs-cell)
                (vectorv-immutable^ _ abs-cell))
            (yield-delay vrσ abs-cell)]
           [(or (? vector^?) (? vector-immutable^?))
            (yield ●)]
           [(and (? immutable?) (? vector?))
            (cond [(number^? z)
                   (yield (list->set (map widen (vector->list vec))))]
                  [(and (<= 0 z) (< z (vector-length vec)))
                   (yield (set (vector-ref vec z)))]
                  [else
                   (log-info "Immutable vector accessed out of bounds")
                   (continue)])]
           [_ (error 'vectorv-ref "WHAT ~a" vec)]))

       (define/read (carv caσ p)
         (match p
           [(consv A _) (yield-delay caσ A)]
           [(? cons^?) (yield ●)]))
       (define/read (cdrv cdσ p)
         (match p
           [(consv _ D) (yield-delay cdσ D)]
           [(? cons^?) (yield ●)]))

       (define/read (core-hashv-ref hσ h k)
         (error 'durp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that write the store
       (define/write (vectorv-set! !σ l δ vec i val)
         (match vec
           [(vectorv _ addrs)
            (cond [(number^? i)
                   (error 'vectorv-set! "Abstract vectors should have a single cell")]
                  [(or (< z 0) (>= z (length addrs)))
                   (log-info "vectorv-set! out out bounds")
                   (continue)]
                  [else (do (!σ) ([σ*-vec #:join !σ (list-ref addrs i) (force !σ val)])
                          (yield (void)))])]
           [(vectorv^ _ abs-cell)
            (do (!σ) ([σ*-vec^ #:join !σ abs-cell (force !σ val)])
              (yield (void)))]
           ;; FIXME: val should "escape"
           [(? vector^?) (yield (void))]
           [_ 
            (log-info "vectorv-set! used on immutable vector")
            (continue)]))

       (define-simple-macro* (mk-vector-constructor name abs conc)
         (define-simple-macro* (name vσ l δ vs)
           (match (widen (length vs))
             [(? number^?)
              (define V-addr (make-var-contour `(V . ,l) δ))
              (do (vσ) loop ([v vs])
                  (match v
                    ['() (yield (abs number^ V-addr))]
                    [(cons v vrest)
                     (do (vσ) ([σ*-pv^ #:join vσ V-addr (force vσ v)])
                       (loop σ*-pv^ vrest))]))]
             [size
              (do (vσ) loop ([v vs] [i 0] [addrs '()])
                  (match v
                    ['() (yield (conc size (reverse addrs)))]
                    [(cons v vrest)
                     (define addr (make-var-contour `(V ,i . ,l) δ))
                     (do (vσ) ([σ*-pv #:join vσ addr (force vσ v)])
                       (loop σ*-pv vrest (add1 i) (cons addr addrs)))]))])))
       (mk-vector-constructor prim-vectorv vectorv^ vectorv)
       (mk-vector-constructor prim-vectorv-immutable vectorv-immutable^ vectorv-immutable)

       (define/write (make-vectorv vσ l δ size [default 0])
         (match (widen size)
           [(? number^?)
            (define V-addr (make-var-contour `(V . ,l) δ))
            (do (vσ) ([σ*-mv^ #:join vσ V-addr (force vσ default)])
              (yield (vectorv^ size V-addr)))]
           [_ (define V-addrs
                (for/list ([i (in-range size)]) (make-var-contour `(V ,i . ,l) δ)))
              (do (vσ) ([σ*-mv #:join* vσ V-addrs (make-list size (force vσ default))])
                (yield (vectorv size V-addrs)))]))

       (define-simple-macro* (make-vector^ vσ l δ vs)
         (let ([V-addr (make-var-contour `(V . ,l) δ)])
           (do (vσ) loop ([v vs]) 
               (match v
                 ['() (yield (vectorv-immutable^ number^ V-addr))]
                 [(cons v vrest)
                  (do (vσ) ([jσ #:join vσ V-addr (force vσ v)])
                    (loop jσ vrest))]))))

       (define/write (make-consv cσ l δ v0 v1)
         (let ([A-addr (make-var-contour `(A . ,l) δ)]
               [D-addr (make-var-contour `(D . ,l) δ)])
           (do (cσ) ([σ*A #:join cσ A-addr (force cσ v0)]
                     [σ*D #:join σ*A D-addr (force σ*A v1)])
             (yield (consv A-addr D-addr)))))

       (define-simple-macro* (make-list^ cσ l δ vs)
         (let ([A-addr (make-var-contour `(A . ,l) δ)]
               [D-addr (make-var-contour `(D . ,l) δ)])
           (define val (consv A-addr D-addr))
           (do (cσ) ([nilσ #:join cσ D-addr (∪1 snull val)])
             (do (nilσ) loop ([v vs] [J ⊥])
                 (match v
                   ['()
                    (do (nilσ) ([jσ #:join nilσ A-addr (singleton J)])
                      (yield val))]
                   [(cons v vrest)
                    (loop nilσ vrest (big⊓ (force nilσ v) J))])))))

       (define-simple-macro* (make-improper^ cσ l δ vs)
         (let ([A-addr (make-var-contour `(A . ,l) δ)]
               [D-addr (make-var-contour `(D . ,l) δ)])
           (define val (consv A-addr D-addr))
           (do (cσ) ([lastσ #:join cσ D-addr (⊓1 (force cσ (car vs)) val)])
             (do (lastσ) loop ([v (cdr vs)] [J ⊥])
                 (match v
                   ['()
                    (do (lastσ) ([jσ #:join lastσ A-addr (singleton J)])
                      (yield val))]
                   [(cons v vrest)
                    (loop lastσ vrest (big⊓ (force lastσ v) J))])))))
       
       (define/write (set-car!v a!σ l δ p v)
         (match p
           [(consv A _)
            (do (aσ) ([σ*a! #:join a!σ A (force a!σ v)])
              (yield (void)))]
           ;; FIXME: v should escape.
           [(? cons^?) (yield (void))]))
       (define/write (set-cdr!v d!σ l δ p v)
         (match p
           [(consv _ D)
            (do (aσ) ([σ*d! #:join d!σ D (force d!σ v)])
              (yield (void)))]
           ;; FIXME: v should escape.
           [(? cons^?) (yield (void))]))

       (define/write (hashv-set hσ l δ h k v)
         (cond [(immutable-hash? h)
                (define P-addr (make-var-contour `(P . ,l) δ))
                (define K-addr (make-var-contour `(K . ,l) δ))
                (define V-addr (make-var-contour `(V . ,l) δ))
                (do (hσ) ([σ*P #:join hσ P-addr (singleton h)]
                          [σ*K #:join σ*P K-addr (force σ*P k)]
                          [σ*V #:join σ*K V-addr (force σ*K v)])
                  (yield (hash-with (hashv-kind h) P-addr K-addr V-addr)))]
               [(hash? h) (error 'hashv-set "Fail gracefully from literal to abstract value ~a ~a ~a" h k v)]
               [else
                (log-info "hashv-set non-hash")
                (continue)]))

       (define/write (hashv-remove hσ l δ h k)
         (cond [(immutable-hash? h)
                (define P-addr (make-var-contour `(P . ,l) δ))
                (define K-addr (make-var-contour `(K . ,l) δ))
                (do (hσ) ([σ*P #:join hσ P-addr (singleton h)]
                          [σ*K #:join σ*P K-addr (force σ*P k)])
                  (yield (hash-without (hashv-kind h) P-addr K-addr)))]
               [(hash? h) (error 'hashv-remove "Fail gracefully from literal to abstract value ~a ~a ~a" h k v)]
               [else
                (log-info "hashv-remove non-hash")
                (continue)]))

       (define/write (hashv-set! h!σ l δ h k v) (error 'TODO-hash-set!))
       (define/write (hashv-remove! h!σ l δ h k v) (error 'TODO-hash-remove!))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; I/O
       (define-simple-macro* (mk-port-open name port^ open-port)
         (define/write (name ioσ l δ s)
           (match (widen s)
             [(? string^?)
              (define status-addr (make-var-contour `(Port . ,l) δ))
              (do (ioσ) ([openσ #:join ioσ status-addr (singleton open@)])
                (yield (port^ status-addr)))]
             [s (yield (open-port s))])))
       (mk-port-open open-input-filev input-port^ open-input-file)
       (mk-port-open open-output-filev output-port^ open-output-file)

       (define-simple-macro* (mk-port-close name port^ close-port)
         (define/write (name ioσ l δ ip)
           (match ip
             [(port^ status)
              (do (ioσ) ([closeσ #:join ioσ status (singleton closed@)])
                (yield (void)))]
             [ip (close-port ip)
                 (yield (void))])))
       (mk-port-close close-input-portv input-port^ close-input-port)
       (mk-port-close close-output-portv output-port^ close-output-port)

       (define/read (port-closed?v ioσ prt)
         (match prt
           [(or (input-port^ status-addr) (output-port^ status-addr))
            (do (ioσ) ([status (getter ioσ status-addr)])
              (yield (eq? status 'closed)))]
           [real-port (yield (port-closed? real-port))]))
       ;; FIXME: optional argument version should be in add-lib
       (define-simple-macro* (mk-writer name writer)
         (define/read (name ioσ any op)
           (match op
             [(output-port^ status-addr)
              (do (ioσ) ([status (getter ioσ status-addr)])
                (case status
                  [(open) (yield (void))]
                  [(closed) (continue)]
                  [else (error 'name "Bad port status ~a" status)]))]
             [real-port
              (cond [(port-closed? real-port) (continue)]
                    [else
                     (do (ioσ) loop ([vs (set->list (force ioσ any))])
                         (match vs
                           ['() (yield (void))]
                           [(cons v vs)
                            (writer v real-port)
                            (loop ioσ vs)]
                           [_ (error 'name "What. ~a" vs)]))])])))
       (mk-writer writev write)
       (mk-writer displayv display)

       ;; XXX: WHAT DO?
       (define/read (readv rσ ip)
         (do (rσ) ([v (in-list (list cons^ vector-immutable^
                                     number^ string^ char^ symbol^
                                     '() eof (void)))])
           (yield v)))

       (define/read (newlinev ioσ op)
         (match op
           [(output-port^ status-addr)
            (do (ioσ) ([status (getter ioσ status-addr)])
              (case status
                [(open) (yield (void))]
                [(closed) (continue)]
                [else (error 'newlinev "Bad port status ~a" status)]))]
           [real-port
            (cond [(port-closed? real-port) (continue)]
                  [else (newline op)
                        (yield (void))])]))
       ;; FIXME: remove for time-apply
       (define/basic (timev any) (yield any)))))

(define-for-syntax prim-table
  #'(;; Numbers
     [add1 #:simple (n -> n) #:widen]
     [sub1 #:simple (n -> n) #:widen]
     [+    #:simple (#:rest n -> n) #:widen]
     [-    #:simple (#:rest n -> n) #:widen]
     [*    #:simple (#:rest n -> n) #:widen]
     [=    #:simple (n #:rest n -> b)]
     [<    #:simple (r #:rest r -> b)]
     [>    #:simple (r #:rest r -> b)]
     [<=    #:simple (r #:rest r -> b)]
     [>=    #:simple (r #:rest r -> b)]
     [quotient #f #f quotientv (z z -> z)]
     [remainder #f #f remainderv (z z -> z)]
     [modulo #f #f modulov (z z -> z)]
     [abs #:simple (r -> r)]
     [min #:simple (r #:rest r -> r)]
     [max #:simple (r #:rest r -> r)]
     [gcd #:simple (#:rest r -> r)]
     [lcm #:simple (#:rest r -> r)]
     [round #:simple (r -> z)]
     [floor #:simple (r -> z)]
     [ceiling #:simple (r -> z)]
     [even? #:simple (z -> b)]
     [odd? #:simple (z -> b)]
     [expt #:simple (n n -> n)]
     [sqrt #:simple (n -> n)]
     [unsafe-fx= #:simple (fx fx -> b)]
     [unsafe-fx< #:simple (fx fx -> b)]
     [unsafe-fx> #:simple (fx fx -> b)]
     [unsafe-fx<= #:simple (fx fx -> b)]
     [unsafe-fx>= #:simple (fx fx -> b)]
     [unsafe-fx- #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fx+ #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fx* #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxquotient #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxremainder #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxmodulo #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxabs #:simple (fx fx -> fx)] ;; XXX: could crash?
     [unsafe-fxmin #:simple (fx fx -> fx)]
     [unsafe-fxmax #:simple (fx fx -> fx)]
     [unsafe-fxand #:simple (fx fx -> fx) #:widen]
     [unsafe-fxxor #:simple (fx fx -> fx) #:widen]
     [unsafe-fxior #:simple (fx fx -> fx) #:widen]
     [unsafe-fxnot #:simple (fx -> fx) #:widen]
     [unsafe-fxlshift #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [unsafe-fxrshift #:simple (fx fx -> fx) #:widen] ;; XXX: could crash?
     [number? #:predicate n]
     [integer? #:predicate z]
     [rational? #:predicate r]
     [zero? #:simple (n -> b)]
     ;; Generic Comparisons
     [equal? #t #f equalv? (any any -> b)]
     [eqv? #t #f equalv? (any any -> b)]
     [eq? #t #f equalv? (any any -> b)]
     ;; Vectors
     [vector #f #t prim-vectorv (#:rest any -> v)]
     [vector-immutable #f #t prim-vectorv-immutable (#:rest any -> v)]
     [qvector^ #f #t make-vector^ (#:rest any -> v)]
     [make-vector #f #t make-vectorv ((z -> v)
                                      (z any -> v))]
     [vector-ref #t #f vectorv-ref (v z -> any)]
     [vector-set! #f #t vectorv-set! (v z any -> !)]
     [vector-length #f #f vectorv-length (v -> z)]
     [vector? #:predicate v]
     ;; Strings
     [string? #:predicate s]
     [string->symbol #:simple (s -> y)]
     [string=? #:simple (s #:rest s -> b)]
     [string>? #:simple (s #:rest s -> b)]
     [string<? #:simple (s #:rest s -> b)]
     [string>=? #:simple (s #:rest s -> b)]
     [string<=? #:simple (s #:rest s -> b)]
     [string-ci=? #:simple (s #:rest s -> b)]
     [string-ci>? #:simple (s #:rest s -> b)]
     [string-ci<? #:simple (s #:rest s -> b)]
     [string-ci>=? #:simple (s #:rest s -> b)]
     [string-ci<=? #:simple (s #:rest s -> b)]
     [string-append #:simple (#:rest s -> s) #:widen]
     [number->string #:simple (n -> (∪ s false)) #:widen]
     ;; Characters
     [char? #:predicate c]
     [char=? #:simple (c #:rest c -> b)]
     [char<? #:simple (c #:rest c -> b)]
     [char>? #:simple (c #:rest c -> b)]
     [char>=? #:simple (c #:rest c -> b)]
     [char<=? #:simple (c #:rest c -> b)]
     [char-ci=? #:simple (c #:rest c -> b)]
     [char-ci<? #:simple (c #:rest c -> b)]
     [char-ci>? #:simple (c #:rest c -> b)]
     [char-ci>=? #:simple (c #:rest c -> b)]
     [char-ci<=? #:simple (c #:rest c -> b)]
     [char-alphabetic? #:simple (c -> b)]
     [char-numeric? #:simple (c -> b)]
     [char-whitespace? #:simple (c -> b)]
     [char-lower-case? #:simple (c -> b)]
     [char-upper-case? #:simple (c -> b)]
     [char->integer #:simple (c -> z) #:widen]
     [integer->char #:simple (z -> c) #:widen]
     [char-upcase #:simple (c -> c) #:widen]
     [char-downcase #:simple (c -> c) #:widen]
     ;; Symbols
     [symbol? #:predicate y]
     [symbol->string #:simple (y -> s)]
     ;; Procedures
     [procedure? #f #f procedure?v (any -> b)]
     ;; Imperative stuff
     [void? #:predicate !]
     [void #:simple (-> !)]
     [error #f #f errorv (#:rest any -> any)]
     ;; Booleans
     [not #:predicate false]
     [boolean? #:predicate b]
     ;; Pairs/lists
     [cons #f #t make-consv (any any -> p)]
     [qlist^ #f #t make-list^ (#:rest any -> lst)]
     [qimproper^ #f #t make-improper^ (any #:rest any -> lst)]
     [pair? #:predicate p]
     [null? #:predicate null]
     [set-car! #f #t set-car!v (p any -> !)]
     [set-cdr! #f #t set-cdr!v (p any -> !)]
     [car    #t #f carv    (p -> any)]
     [cdr    #t #f cdrv    (p -> any)]
     ;; Ports
     [input-port? #:predicate ip]
     [output-port? #:predicate op]
     [open-input-file #f #t open-input-filev (s -> ip)]
     [open-output-file #f #t open-output-filev (s -> op)]
     [close-input-port #f #t close-input-portv (ip -> !)]
     [close-output-port #f #t close-output-portv (op -> !)]
     [port-closed? #t #f port-closed?v (prt -> b)]
#;#;
     [current-input-port #f #f current-input-portv (-> ip)]
     [current-output-port #f #f current-input-portv (-> op)]
     [read #t #f readv ((-> lst) ;; XXX: impoverished read
                        (ip -> lst))]
     [write #t #f writev ((any -> !)
                          (any op -> !))]
     [display #t #f displayv (any op -> !)]
     [newline #t #f newlinev ((-> !)
                              (op -> !))]
     [eof-object? #:predicate eof]
     ;; time should be with time-apply, but that means supporting apply...
     [time #f #f timev (any -> any)]
     ;; Hashes
     [hash-equal?   #f #f hashv-equal?     (h -> b)]
     [hash-eqv?     #f #f hashv-eqv?       (h -> b)]
     [hash-eq?      #f #f hashv-eq?        (h -> b)]
     [hash-set      #f #t hashv-set        (h any any -> h)]
     [hash-remove   #f #t hashv-remove     (h any -> h)]
#;#;#;#;#;#;#;
     [core-hash-ref #t #f hashv-ref        (h any -> any)]
     [hash-has-key? #t #f hashv-has-key?   (h any -> b)]
     [hash-set!     #f #t hashv-set!       (h any any -> !)]
     [hash-remove!  #f #t hashv-remove!    (h any -> !)]
     [make-hash     #f #t make-hashv-equal ((-> h)
                                            (lst -> h))]
     [make-hasheqv  #f #t make-hashv-eqv   ((-> h)
                                            (lst -> h))]
     [make-hasheq   #f #t make-hashv-eq    ((-> h)
                                            (lst -> h))]
     [immutable?    #f #f immutablev?      (any -> b)]))

(define-syntax (mk-prims stx)
  (syntax-parse stx
    [(_ (~and #:static static?) primitive?:id changes-store?:id reads-store?:id)
     (quasisyntax/loc stx
       (mk-static-primitive-functions
        primitive? changes-store? reads-store? #,prim-table))]
    [(_ global-σ?:boolean mean:id clos?:id rlos?:id)
     (quasisyntax/loc stx
       (mk-primitive-meaning global-σ? mean #,@(prim-defines #'clos? #'rlos?) #,prim-table))]))

(mk-prims #:static primitive? changes-store? reads-store?)

(define prim-constants
  (hasheq 'eof eof
          'null '()
          'true #t
          'false #f))