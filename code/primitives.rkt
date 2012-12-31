#lang racket

(require "data.rkt" "notation.rkt" "do.rkt" "parameters.rkt"
         "primitive-maker.rkt" "egal-box.rkt"
         (for-syntax racket/syntax syntax/parse) ;; for core syntax-classes
         racket/stxparam
         racket/unsafe/ops
         racket/fixnum
         racket/flonum)
(provide primitive? primitive? prim-constants prim-arities arity-error
         (for-syntax mk-mk-prims)
         define/read define/basic define/write yield-both alt-reverse
         prim-meaning
         ;; reprovide
         snull yield getter widen prim-extras)

(define-syntax-parameter prim-meaning #f)

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

(define-for-syntax (prim-defines clos rlos kont? K ev co)
  (with-syntax ([clos? (format-id clos "~a?" clos)]
                [rlos? (format-id rlos "~a?" rlos)]
                [clos: (format-id clos "~a:" clos)]
                [rlos: (format-id rlos "~a:" rlos)]
                [ev ev]
                [co co]
                [(δ-op ...) (if (zero? K) #'() #'(δ))]
                [kont? kont?])
    #`((define-syntax-rule (yield-delay ydσ v)
         (do (ydσ) ([v* #:in-delay ydσ v]) (yield v*)))
       (define-simple-macro* (errorv prσ vs)
         (begin (log-info "Error reachable ~a" (for/list ([v (in-list vs)])
                                                 (match v
                                                   [(addr a) (getter prσ a)]
                                                   [(value-set s) s]
                                                   [_ v])))
                (continue)))

       (define-simple-macro* (printfv prσ vs)
         (begin (do-comp #:bind/extra (vlst)
                         (do (prσ) loop ([acc '()] [-vs vs])
                             (match -vs
                               [(cons v -vs)
                                (match v
                                  [(addr a)
                                   (do (prσ) ([s #:get prσ a])
                                     (loop prσ (cons s acc) -vs))]
                                  [(value-set s) (loop prσ (cons s acc) -vs)]
                                  [_ (loop prσ (cons v acc) -vs)])]
                               ['() (do-values (alt-reverse acc))]))
                         (begin (log-debug "Printing: ~a" vlst)
                                (yield (void))))))

       (define/basic (procedure?v v) (yield (or (clos? v) (rlos? v))))
       (define/basic (vectorv-length v)
         (match v
           [(or (vectorv len _) (vectorv^ len _)
                (vectorv-immutable len _) (vectorv-immutable^ len _)) (yield len)]
           [(or (? vector^?) (? vector-immutable^?) (? qvector^?)) (yield number^)]
           [(== vec0) (yield 0)]
           [_ (yield (vector-length v))]))

       ;; Not a general predicate. Only for immutable hashes, vectors, strings, byte-strings and boxes.
       ;; Currently we have only immutable hashes.
       (define/basic (immutablev? v)
         (match v
           [(or (? vectorv-immutable^?)
                (? vector-immutable^?)
                (== vec0)
                (? immutable? (? vector?)))
            (yield #t)]
           [_ (yield #f)]))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that read the store

       (define/read (equalv? eσ v0 v1)
         (define-syntax-rule (both-if pred) (if pred (yield-both eσ) (yield #f)))
         (do (eσ) ([v0 #:in-force eσ v0]
                   [v1 #:in-force eσ v1])
           (match* (v0 v1)
             [((== ●) _) (yield-both eσ)]
             [(_ (== ●)) (yield-both eσ)]
             [((== qdata^) (or (== vec0) (== qvector^) (? vector?) (? vectorv-immutable^?) (? vectorv-immutable?)
                               (== cons^) (== qcons^)
                               (? atomic?)))
              (yield-both eσ)]
             [((or (== vec0) (== qvector^) (? vector?) (? vectorv-immutable^?) (? vectorv-immutable?)
                   (== cons^) (== qcons^)
                   (? atomic?))
               (== qdata^))
              (yield-both eσ)]
             [((? clos?) _) (both-if (clos? v1))]
             [(_ (? clos?)) (yield #f)] ;; first not a closure
             [((? rlos?) _) (both-if (rlos? v1))]
             [(_ (? rlos?)) (yield #f)]
             [((or (== cons^) (? consv?) (== qcons^)) _)
              (both-if (or (consv? v1) (eq? v1 cons^) (eq? v1 qcons^)))] ;; FIXME: overapproximate for concrete
             [(_ (or (== cons^) (? consv?))) (yield #f)] ;; first not a cons
             ;; next 4 clauses handle 0-length vectors specifically
             [((== vec0) _) (yield (or (eq? v1 vec0)
                                       (and (vector? v1)
                                            (zero? (vector-length v1)))))]
             [(_ (== vec0)) (yield (or (eq? v0 vec0)
                                       (and (vector? v0)
                                            (zero? (vector-length v0)))))]
             [((? vector?) _) (=> fail) (if (zero? (vector-length v0))
                                            (yield (or (eq? v1 vec0) (equal? v0 v1)))
                                            (fail))]
             [(_ (? vector?)) (=> fail) (if (zero? (vector-length v1))
                                            (yield (or (eq? v0 vec0) (equal? v0 v1)))
                                            (fail))]
             [((or (== vector^) (== vector-immutable^)
                   (== qvector^)
                   (? vector?) ;; Racket's immutable vectors
                   (? vectorv-immutable^?) (? vectorv?)
                   (? vectorv^?) (? vectorv-immutable?)) _)
              (both-if (or (vectorv? v1) (vectorv-immutable? v1) (eq? v1 vector^)
                           (eq? qvector^ v1)
                           (eq? v1 vector-immutable^)
                           (vector? v1)
                           (vectorv-immutable^? v1)))] ;; FIXME: not right for concrete
             [(_ (or (== vector^) (== vector-immutable^) (== qvector^)
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
           [(or (? vector^?) (? vector-immutable^?)) (yield ●)]
           [(? qvector^?) (yield qdata^)]
           [(== vec0)
            (log-info "Cannot reference any cells in a 0-length vector")
            (continue)]
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
           [(? qcons^?) (yield qdata^)]
           [(? cons^?) (yield ●)]))
       (define/read (cdrv cdσ p)
         (match p
           [(consv _ D) (yield-delay cdσ D)]
           [(? qcons^?) (yield qdata^)]
           [(? cons^?) (yield ●)]))

       ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ;; Prims that write the store
       (define/write (vectorv-set! !σ l δ vec i val)
         (match vec
           [(vectorv _ addrs)
            (cond [(number^? i)
                   (error 'vectorv-set! "Abstract vectors should have a single cell")]
                  [(or (< z 0) (>= z (length addrs)))
                   (log-info "vectorv-set! out out bounds")
                   (continue)]
                  [else (do (!σ) ([σ*-vec #:join-forcing !σ (list-ref addrs i) val])
                          (yield (void)))])]
           [(vectorv^ _ abs-cell)
            (do (!σ) ([σ*-vec^ #:join-forcing !σ abs-cell val])
              (yield (void)))]
           ;; FIXME: val should "escape"
           [(? vector^?) (yield (void))]
           [(== vec0)
            (log-info "Cannot set any cells in a 0-length vector")
            (continue)]
           [_
            (log-info "vectorv-set! used on immutable vector")
            (continue)]))

       (define-simple-macro* (mk-vector-constructor name abs conc)
         (define-simple-macro* (name vσ l δ vs)
           (cond [(null? vs) (yield vec0)]
                 [else
                  (match (widen (length vs))
                    [(? number^?)
                     (define V-addr (make-var-contour `(V . ,l) δ))
                     (do (vσ) loop ([v vs])
                         (match v
                           ['()
                            (yield (abs number^ V-addr))]
                           [(cons v vrest)
                            (do (vσ) ([σ*-pv^ #:join-forcing vσ V-addr v])
                              (loop σ*-pv^ vrest))]))]
                    [size
                     (do (vσ) loop ([v vs] [i 0] [addrs '()])
                         (match v
                           ['() (yield (conc size (reverse addrs)))]
                           [(cons v vrest)
                            (define addr (make-var-contour `(V ,i . ,l) δ))
                            (do (vσ) ([σ*-pv #:join-forcing vσ addr v])
                              (loop σ*-pv vrest (add1 i) (cons addr addrs)))]))])])))

       (mk-vector-constructor prim-vectorv vectorv^ vectorv)
       (mk-vector-constructor prim-vectorv-immutable vectorv-immutable^ vectorv-immutable)

       (define/write (make-vectorv vσ l δ size [default 0])
         (cond [(and (exact-integer? size) (= 0 size)) (yield vec0)]
               [else
                (match (widen size)
                  [(? number^?)
                   (define V-addr (make-var-contour `(V . ,l) δ))
                   (do (vσ) ([σ*-mv^ #:join-forcing vσ V-addr default])
                     (yield (vectorv^ size V-addr)))]
                  [_ (define V-addrs
                       (for/list ([i (in-range size)]) (make-var-contour `(V ,i . ,l) δ)))
                     (do (vσ) ([fs #:force vσ default]
                               [σ*-mv #:join* vσ V-addrs (make-list size fs)])
                       (yield (vectorv size V-addrs)))])]))

       (define/write (vectorv->list vlσ l δ v)
         (match v
           [(== vec0) (yield '())]
           [(vectorv len addrs) (error 'TODO "concrete vector->list")]
           [(or (vectorv^ len addr)
                (vectorv-immutable^ len addr))
            (define A-addr (make-var-contour `(A . ,l) δ))
            (define D-addr (make-var-contour `(D . ,l) δ))
            (define val (consv A-addr D-addr))
            (do (vlσ) ([cσ #:alias vlσ A-addr addr]
                       [cσ* #:join cσ D-addr (⊓1 snull val)])
              (yield val))]
           [(or (? vectorv^?) (== vector-immutable^))
            (do (vlσ) ([out (in-list (list cons^ '()))])
              (yield out))]
           [(? vector?) (error 'TODO "vector literal->list")]))

       (define/write (list->vectorv lvσ l δ lst)
         (match lst
           ['() (yield vec0)]
           [(== cons^) (yield vector^)]
           [(or (? qcons^?) (== ●))
            (do (lvσ) ([out (in-list (list vec0 vector^))])
              (yield out))]
           [(consv A D)
            #,(if (= +inf.0 K)
                #'(error 'TODO "concrete list->vector")
                #'(let ([cell (make-var-contour `(V . ,l) δ)]
                        [seen (make-hash)])
                    (do (lvσ) loop ([todo (set lst)])
                        (cond [(∅? todo) (yield (vectorv^ number^ cell))]
                              [else
                               (do (lvσ) ([val (in-set todo)]
                                          #:unless (hash-has-key? seen val))
                                 (hash-set! seen val #t)
                                 (match val
                                   [(? cons^?)
                                    (do (lvσ) ([σ* #:join lvσ cell (singleton ●)])
                                      (loop σ* (todo . ∖1 . val)))]
                                   [(? qcons^?)
                                    (do (lvσ) ([σ* #:join lvσ cell (singleton qdata^)])
                                      (loop σ* (todo . ∖1 . val)))]
                                   [(consv A D)
                                    (do (lvσ) ([σ* #:alias lvσ cell A]
                                               [more #:get σ* D])
                                      (loop σ* ((∪ todo more) . ∖1 . val)))]
                                   [_
                                    (unless (null? val)
                                      (log-info "list->vector input non-list. Tail: ~a" val))
                                    (continue)]))]))))]))

       ;; INVARIANT: internal, so never 'apply'd.
       (define-simple-macro* (make-vector^ vσ l δ vs)
         (cond [(null? vs) (yield vec0)]
               [else
                (define V-addr (make-var-contour `(V . ,l) δ))
                (do (vσ) loop ([v vs])
                    (match v
                      ['() (yield (vectorv-immutable^ number^ V-addr))]
                      [(cons v vrest)
                       (do (vσ) ([jσ #:join-forcing vσ V-addr v])
                         (loop jσ vrest))]))]))

       (define/write (make-consv cσ l δ v0 v1)
         (let ([A-addr (make-var-contour `(A . ,l) δ)]
               [D-addr (make-var-contour `(D . ,l) δ)])
           (do (cσ) ([σ*A #:join-forcing cσ A-addr v0]
                     [σ*D #:join-forcing σ*A D-addr v1])
             (yield (consv A-addr D-addr)))))

       ;; INVARIANT: internal, so never 'apply'd.
       (define-simple-macro* (make-list^ cσ l δ vs)
         (let ([A-addr (make-var-contour `(A . ,l) δ)]
               [D-addr (make-var-contour `(D . ,l) δ)])
           (define val (consv A-addr D-addr))
           (do (cσ) ([nilσ #:join cσ D-addr (⊓1 snull val)])
             (do (nilσ) loop ([v vs] [J ⊥])
                 (match v
                   ['()
                    (do (nilσ) ([jσ #:join nilσ A-addr (singleton J)])
                      (yield val))]
                   [(cons v vrest)
                    (do (nilσ) ([fs #:force nilσ v])
                      (loop nilσ vrest (big⊓ fs J)))])))))

       ;; INVARIANT: internal, so never 'apply'd.
       (define-simple-macro* (make-improper^ cσ l δ vs)
         (let ([A-addr (make-var-contour `(A . ,l) δ)]
               [D-addr (make-var-contour `(D . ,l) δ)])
           (define val (consv A-addr D-addr))
           (do (cσ) ([fs #:force cσ (car vs)]
                     [lastσ #:join cσ D-addr (⊓1 fs val)])
             (do (lastσ) loop ([v (cdr vs)] [J ⊥])
                 (match v
                   ['()
                    (do (lastσ) ([jσ #:join lastσ A-addr (singleton J)])
                      (yield val))]
                   [(cons v vrest)
                    (do (lastσ) ([fs #:force lastσ v])
                      (loop lastσ vrest (big⊓ fs J)))])))))

       (define/write (set-car!v a!σ l δ p v)
         (match p
           [(consv A _)
            (do (aσ) ([σ*a! #:join-forcing a!σ A v])
              (yield (void)))]
           ;; FIXME: v should escape.
           [(? cons^?) (yield (void))]
           [(? qcons^?)
            (log-info "Cannot set! cons from quote")
            (continue)]))
       (define/write (set-cdr!v d!σ l δ p v)
         (match p
           [(consv _ D)
            (do (aσ) ([σ*d! #:join-forcing d!σ D v])
              (yield (void)))]
           ;; FIXME: v should escape.
           [(? cons^?) (yield (void))]
           [(? qcons^?)
            (log-info "Cannot set! cons from quote")
            (continue)]))

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
            (do (ioσ) ([status #:in-get ioσ status-addr])
              (yield (eq? status closed@)))]
           [real-port (yield (port-closed? real-port))]))
       ;; FIXME: optional argument version should be in add-lib
       (define-simple-macro* (mk-writer name writer)
         (define-simple-macro* (name ioσ vs)
           (match vs
             [(list any) (yield (void))] ;; fixme
             [(list any op)
              (match op
                [(output-port^ status-addr)
                 (do (ioσ) ([status #:in-get ioσ status-addr])
                   (match status
                     [(== open@) (yield (void))]
                     [(== closed@) (continue)]
                     [else (error 'name "Bad port status ~a" status)]))]
                [real-port
                 (cond [(port-closed? real-port) (continue)]
                       [else
                        (do (ioσ) ([fs #:force ioσ any])
                          (do (ioσ) loop ([vs (set->list fs)])
                              (match vs
                                ['() (yield (void))]
                                [(cons v vs)
                                 (writer v real-port)
                                 (loop ioσ vs)]
                                [_ (error 'name "What. ~a" vs)])))])])])))
       (mk-writer writev write)
       (mk-writer displayv display)

       ;; XXX: WHAT DO?
       (define-simple-macro* (readv rσ vs)
         (match vs
           [(or '() (list _))
            (do (rσ) ([v (in-list (list cons^ vector-immutable^ vec0
                                        number^ string^ char^ symbol^
                                        #t #f '() eof (void)))])
              (yield v))]))

       (define-simple-macro* (newlinev ioσ vs)
         (match vs
           [(list) (yield (void))] ;; FIXME
           [(list op)
            (match op
              [(output-port^ status-addr)
               (do (ioσ) ([status #:in-get ioσ status-addr])
                 (match status
                   [(== open@) (yield (void))]
                   [(== closed@) (continue)]
                   [else (error 'newlinev "Bad port status ~a" status)]))]
              [real-port
               (cond [(port-closed? real-port) (continue)]
                     [else (newline op)
                           (yield (void))])])]))
       ;; FIXME: remove for time-apply
       (define/basic (timev any) (yield any))

       (mk-pull-arguments pull-arguments (δ-op ...) #f)
       ;; XXX: Rest-args and can be 'apply'd (FIXME)
       (define-simple-macro* (internal-applyv iapσ l δ k vs)
         (let* ([-vs vs]
                [f (unsafe-car -vs)]
                [args (unsafe-cdr -vs)])
           (match-function f
             [(clos: xs e ρ)
              (do-comp #:bind/extra (#:σ nσ apply-addrs)
                       (tapp pull-arguments #:σ iapσ xs #f l δ-op ... args)
                       (if apply-addrs
                           (do (nσ) ([(ρ* σ*-apcl δ*) #:bind ρ nσ l δ xs apply-addrs])
                             (original-yield (ev σ*-apcl e ρ* k δ)))
                           (continue)))]
             [(rlos: xs r e ρ)
              (do-comp #:bind/extra (#:σ nσ apply-addrs)
                       (tapp pull-arguments #:σ iapσ xs #t l δ-op ... args)
                       (if apply-addrs
                           (do (nσ) ([(ρ* σ*-apcl δ*) #:bind-rest-apply ρ nσ l δ xs r apply-addrs])
                             (original-yield (ev σ*-apcl e ρ* k δ)))
                           (continue)))]
             [(primop o fallback arity)
              (when (list? arity) (error 'apply "TODO: multi-arity function apply"))
              (define-values (num rest?)
                (match arity
                  [(arity-at-least n) (values n #t)]
                  [n (values n #f)]))
              ;; FIXME: doesn't work with rest-arg primitives
              (do-comp #:bind/extra (#:σ nσ apply-addrs)
                       (tapp pull-arguments #:σ iapσ num rest? l δ-op ... args)
                       (if apply-addrs
                           (tapp prim-meaning #:σ nσ o (eunbox fallback) rest? l δ-op ... k apply-addrs)
                           (continue)))]
             [(? kont?)
              (do-comp #:bind/extra (#:σ nσ apply-addrs)
                       (tapp pull-arguments #:σ iapσ 1 #f l δ-op ... args)
                       (match apply-addrs
                         [(list a)
                          (do (nσ) ([v #:in-delay nσ a])
                            (original-yield (co nσ f v)))]
                         [_ (continue)]))]))))))



(define-for-syntax prim-table
  #'([apply #:!! internal-applyv (fn #:rest any -> any)]
     ;; Numbers
     [add1 #:simple (n -> n) #:widen]
     [sub1 #:simple (n -> n) #:widen]
     [unary-- #:simple-alternative - (n -> n) #:widen]
     [binary-+ #:simple-alternative + (n n -> n) #:widen]
     [binary-- #:simple-alternative - (n n -> n) #:widen]
     [binary-* #:simple-alternative * (n n -> n) #:widen]
     [binary-/ #:simple-alternative / (n n -> n) #:widen #:guard exn:fail:contract:divide-by-zero?]
     [- #:simple (n #:rest n -> n) #:widen]
     [+ #:simple (#:rest n -> n) #:widen]
     [* #:simple (#:rest n -> n) #:widen]
     [/ #:simple (n #:rest n -> n) #:widen #:guard exn:fail:contract:divide-by-zero?]
     [quotient #:simple (z z -> z) #:widen #:guard exn:fail:contract:divide-by-zero?]
     [remainder #:simple (z z -> z) #:widen #:guard exn:fail:contract:divide-by-zero?]
     [modulo #:simple (z z -> z) #:widen #:guard exn:fail:contract:divide-by-zero?]
     [= #:simple (n n #:rest n -> b)]
     [< #:simple (r r #:rest r -> b)]
     [> #:simple (r r #:rest r -> b)]
     [<= #:simple (r r #:rest r -> b)]
     [>= #:simple (r r #:rest r -> b)]
     [binary-bitwise-and #:simple-alternative bitwise-and (z z -> z) #:widen]
     [binary-bitwise-xor #:simple-alternative bitwise-xor (z z -> z) #:widen]
     [binary-bitwise-ior #:simple-alternative bitwise-ior (z z -> z) #:widen]
     [bitwise-and #:simple (#:rest z -> z) #:widen]
     [bitwise-ior #:simple (#:rest z -> z) #:widen]
     [bitwise-xor #:simple (#:rest z -> z) #:widen]
     [bitwise-not #:simple (z -> z)]
     [numerator #:simple (q -> z)]
     [denominator #:simple (q -> z)]
     [make-rectangular #:simple (r r -> n)]
     [make-polar #:simple (r r -> n)]
     [real-part #:simple (n -> r)]
     [imag-part #:simple (n -> r)]
     [magnitude #:simple (n -> r)]
     [abs #:simple (r -> r)]
     [binary-min #:simple-alternative min (r r -> r)]
     [binary-max #:simple-alternative max (r r -> r)]
     [binary-gcd #:simple-alternative gcd (r r -> r) #:widen]
     [binary-lcm #:simple-alternative lcm (r r -> r) #:widen]
     [min #:simple (r #:rest r -> r)]
     [max #:simple (r #:rest r -> r)]
     [gcd #:simple (#:rest r -> r) #:widen]
     [lcm #:simple (#:rest r -> r) #:widen]
     [expt #:simple (n n -> n) #:widen]
     [exp #:simple (n -> n) #:widen]
     [round #:simple (r -> z) #:widen]
     [floor #:simple (r -> z) #:widen]
     [ceiling #:simple (r -> z) #:widen]
     [even? #:simple (z -> b)]
     [odd? #:simple (z -> b)]
     [expt #:simple (n n -> n) #:widen]
     [sqrt #:simple (n -> n) #:widen]
     [atan #:simple (r r -> n) #:widen]
     [sin #:simple (n -> n) #:widen]
     [cos #:simple (n -> n) #:widen]
     [asin #:simple (n -> n) #:widen]
     [acos #:simple (n -> n) #:widen]
     [log #:simple (n -> n) #:widen]
     [fl+ #:simple (fl fl -> fl) #:widen]
     [fl* #:simple (fl fl -> fl) #:widen]
     [fl/ #:simple (fl fl -> fl) #:widen]
     [fl- #:simple (fl fl -> fl) #:widen]
     [fl= #:simple (fl fl -> b)]
     [fl< #:simple (fl fl -> b)]
     [fl> #:simple (fl fl -> b)]
     [fl<= #:simple (fl fl -> b)]
     [fl>= #:simple (fl fl -> b)]
     [flmin #:simple (fl fl -> fl)]
     [flmax #:simple (fl fl -> fl)]
     [flabs #:simple (fl -> fl)]
     [flround #:simple (fl -> fl) #:widen]
     [flceiling #:simple (fl -> fl) #:widen]
     [flfloor #:simple (fl -> fl) #:widen]
     [fltruncate #:simple (fl -> fl) #:widen]
     [flcos #:simple (fl -> fl) #:widen]
     [flsin #:simple (fl -> fl) #:widen]
     [fltan #:simple (fl -> fl) #:widen]
     [flasin #:simple (fl -> fl) #:widen]
     [flacos #:simple (fl -> fl) #:widen]
     [flasin #:simple (fl -> fl) #:widen]
     [flatan #:simple (fl -> fl) #:widen]
     [fllog #:simple (fl -> fl) #:widen]
     [flexp #:simple (fl -> fl) #:widen]
     [flsqrt #:simple (fl -> fl) #:widen]
     [flexpt #:simple (fl fl -> fl) #:widen]
     [->fl #:simple (z -> fl) #:widen]
     [unsafe-fx= #:simple-alternative fx= (fx fx -> b)]
     [unsafe-fx< #:simple-alternative fx< (fx fx -> b)]
     [unsafe-fx> #:simple-alternative fx> (fx fx -> b)]
     [unsafe-fx<= #:simple-alternative fx<= (fx fx -> b)]
     [unsafe-fx>= #:simple-alternative fx>= (fx fx -> b)]
     [unsafe-fxmin #:simple-alternative fxmin (fx fx -> fx)]
     [unsafe-fxmax #:simple-alternative fxmax (fx fx -> fx)]
     [unsafe-fx- #:simple-alternative fx- (fx fx -> fx) #:widen
                 #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fx+ #:simple-alternative fx+ (fx fx -> fx) #:widen
                 #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fx* #:simple-alternative fx* (fx fx -> fx) #:widen
                 #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxquotient #:simple-alternative fxquotient (fx fx -> fx) #:widen
                        #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxremainder #:simple-alternative fxremainder (fx fx -> fx) #:widen
                         #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxmodulo #:simple-alternative fxmodulo (fx fx -> fx) #:widen
                      #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxabs #:simple-alternative fxabs (fx fx -> fx)
                   #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxand #:simple-alternative fxand (fx fx -> fx) #:widen
                   #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxxor #:simple-alternative fxxor (fx fx -> fx) #:widen
                   #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxior #:simple-alternative fxior (fx fx -> fx) #:widen
                   #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxnot #:simple-alternative fxnot (fx -> fx) #:widen
                   #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxlshift #:simple-alternative fxlshift (fx fx -> fx) #:widen
                      #:guard exn:fail:contract:non-fixnum-result?]
     [unsafe-fxrshift #:simple-alternative fxrshift (fx fx -> fx) #:widen
                      #:guard exn:fail:contract:non-fixnum-result?]
     [number? #:predicate n]
     [complex? #:predicate n]
     [integer? #:predicate z]
     [rational? #:predicate q]
     [fixnum? #:predicate fx]
     [flonum? #:predicate fl]
     [real? #:predicate r]
     [zero? #:simple (n -> b)]
     [exact? #:simple (n -> b)]
     [inexact? #:simple (n -> b)]
     [exact->inexact #:simple (n -> n) #:widen]
     [inexact->exact #:simple (n -> n) #:widen]
     [positive? #:simple (r -> b)]
     [negative? #:simple (r -> b)]
     [inexact-real? #:simple (any -> b)]
     [exact-integer? #:simple (any -> b)]
     [exact-nonnegative-integer? #:simple (any -> b)]
     [exact-positive-integer? #:simple (any -> b)]
     ;; Generic Comparisons
     [equal? #:ro equalv? (any any -> b)]
     [eqv? #:ro equalv? (any any -> b)]
     [eq? #:ro equalv? (any any -> b)]
     ;; Vectors
     [vector #:rw prim-vectorv (#:rest any -> v)]
     [vector-immutable #:rw prim-vectorv-immutable (#:rest any -> v)]
     [qvector^ #:rw make-vector^ (#:rest any -> v)]
     [internal-make-vector #:rw make-vectorv (z any -> v)]
     [vector-ref #:ro vectorv-ref (v z -> any)]
     [vector-set! #:rw vectorv-set! (v z any -> !)]
     [vector-length #:no vectorv-length (v -> z)]
     [vector->list #:rw vectorv->list (v -> lst)]
     [list->vector #:rw list->vectorv (lst -> v)]
     [vector? #:predicate v]
     ;; Strings
     [string? #:predicate s]
     [string->symbol #:simple (s -> y)]
     [binary-string=? #:simple-alternative string=? (s s -> b)]
     [binary-string>? #:simple-alternative string>? (s s -> b)]
     [binary-string<? #:simple-alternative string<? (s s -> b)]
     [binary-string>=? #:simple-alternative string>=? (s s -> b)]
     [binary-string<=? #:simple-alternative string<=? (s s -> b)]
     [binary-string-ci=? #:simple-alternative string-ci=? (s s -> b)]
     [binary-string-ci>? #:simple-alternative string-ci>? (s s -> b)]
     [binary-string-ci<? #:simple-alternative string-ci<? (s s -> b)]
     [binary-string-ci>=? #:simple-alternative string-ci>=? (s s -> b)]
     [binary-string-ci<=? #:simple-alternative string-ci<=? (s s -> b)]
     [binary-string-append #:simple-alternative string-append (s s -> s) #:widen]
     [string=? #:simple (s s #:rest s -> b)]
     [string>? #:simple (s s #:rest s -> b)]
     [string<? #:simple (s s #:rest s -> b)]
     [string>=? #:simple (s s #:rest s -> b)]
     [string<=? #:simple (s s #:rest s -> b)]
     [string-ci=? #:simple (s s #:rest s -> b)]
     [string-ci>? #:simple (s s #:rest s -> b)]
     [string-ci<? #:simple (s s #:rest s -> b)]
     [string-ci>=? #:simple (s s #:rest s -> b)]
     [string-ci<=? #:simple (s s #:rest s -> b)]
     [string-append #:simple (#:rest s -> s) #:widen]
     [number->string #:simple (n -> (∪ s false)) #:widen]
     ;; Characters
     [char? #:predicate c]
     [binary-char=? #:simple-alternative char=? (c c -> b)]
     [binary-char<? #:simple-alternative char<? (c c -> b)]
     [binary-char>? #:simple-alternative char>? (c c -> b)]
     [binary-char>=? #:simple-alternative char>=? (c c -> b)]
     [binary-char<=? #:simple-alternative char<=? (c c -> b)]
     [binary-char-ci=? #:simple-alternative char-ci=? (c c -> b)]
     [binary-char-ci<? #:simple-alternative char-ci<? (c c -> b)]
     [binary-char-ci>? #:simple-alternative char-ci>? (c c -> b)]
     [binary-char-ci>=? #:simple-alternative char-ci>=? (c c -> b)]
     [binary-char-ci<=? #:simple-alternative char-ci<=? (c c -> b)]
     [char=? #:simple (c c #:rest c -> b)]
     [char<? #:simple (c c #:rest c -> b)]
     [char>? #:simple (c c #:rest c -> b)]
     [char>=? #:simple (c c #:rest c -> b)]
     [char<=? #:simple (c c #:rest c -> b)]
     [char-ci=? #:simple (c c #:rest c -> b)]
     [char-ci<? #:simple (c c #:rest c -> b)]
     [char-ci>? #:simple (c c #:rest c -> b)]
     [char-ci>=? #:simple (c c #:rest c -> b)]
     [char-ci<=? #:simple (c c #:rest c -> b)]
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
     [procedure? #:no procedure?v (any -> b)]
     ;; Imperative stuff
     [void? #:predicate !]
     [void #:simple (-> !)]
     [error #:ro errorv (#:rest any -> any)]
     ;; Booleans
     [not #:predicate false]
     [boolean? #:predicate b]
     ;; Pairs/lists
     [cons #:rw make-consv (any any -> p)]
     [qlist^ #:rw make-list^ (#:rest any -> lst)]
     [qimproper^ #:rw make-improper^ (any #:rest any -> lst)]
     [pair? #:predicate p]
     [null? #:predicate null]
     [set-car! #:rw set-car!v (p any -> !)]
     [set-cdr! #:rw set-cdr!v (p any -> !)]
     [car #:ro carv (p -> any)]
     [cdr #:ro cdrv (p -> any)]
     ;; Ports
     [input-port? #:predicate ip]
     [output-port? #:predicate op]
     [open-input-file #:rw open-input-filev (s -> ip)]
     [open-output-file #:rw open-output-filev (s -> op)]
     [close-input-port #:rw close-input-portv (ip -> !)]
     [close-output-port #:rw close-output-portv (op -> !)]
     [port-closed? #:ro port-closed?v (prt -> b)]
#;#;
     [current-input-port #:no current-input-portv (-> ip)]
     [current-output-port #:no current-input-portv (-> op)]
     [read #:ro readv ((-> lst) ;; XXX: impoverished read
                       (ip -> lst))]
     [write #:ro writev ((any -> !)
                         (any op -> !))]
     [display #:ro displayv ((any -> !)
                             (any op -> !))]
     [newline #:ro newlinev ((-> !)
                             (op -> !))]
     [printf #:ro printfv (#:rest any -> !)] ;; for debugging
     [eof-object? #:predicate eof]
     ;; time should be with time-apply, but that means supporting apply...
     [time #:no timev (any -> any)]
     [immutable? #:no immutablev? (any -> b)]))

(define-for-syntax prim-aliases
  #'([apply internal-apply]))

(define-syntax (mk-static-prims stx)
  (syntax-parse stx
    [(_ primitive?:id prim-arities:id)
     (quasisyntax/loc stx
       (mk-static-primitive-functions
        primitive? prim-arities #,prim-table #,prim-aliases))]))

(mk-static-prims primitive? prim-arities)

(define-for-syntax ((mk-mk-prims compiled? global-σ? K) stx)
  (syntax-parse stx
    [(_ mean:id compile:id ev:id co:id ap:id clos:id rlos:id kont?:id extra ...)
     (with-syntax ([clos? (format-id #'clos "~a?" #'clos)])
       (quasisyntax/loc stx
         (mk-primitive-meaning
          #,compiled? #,global-σ? #,(= K 0)
          mean compile ev co ap clos? rlos kont? (extra ...)
          #,@(prim-defines #'clos #'rlos #'kont? K #'ev #'co)
          #,prim-table
          #,prim-aliases)))]))

(define prim-constants
  (hasheq 'eof eof
          'null '()
          'true #t
          'false #f))