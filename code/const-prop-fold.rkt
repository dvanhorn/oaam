#lang racket

(require "ast.rkt"
         "context.rkt"
         "data.rkt"
         "deltas.rkt"
         "fix.rkt"
         "generators.rkt"
         "handle-limits.rkt"
         "imperative.rkt"
         "kcfa.rkt"
         "lazy-strict.rkt"
         "nonsparse.rkt"
         "notation.rkt"
         "parse.rkt" 
         "prealloc.rkt"
         "primitives.rkt"
         "store-passing.rkt"
         racket/match
         racket/splicing
         (for-syntax racket/list
                     racket/match
                     racket/flonum
                     racket/stxparam
                     racket/unsafe/ops
                     "notation.rkt"
                     "ast.rkt"
                     "data.rkt"
                     "primitives.rkt"))

(begin-for-syntax
 (define (value-node?-proc n . pred-apps)
   `(define (value-node? ,n)
      (or (datum? ,n)
          (atomic? ,n)
          (primr? ,n)
          (lam? ,n)
          (rlm? ,n)
          ,@pred-apps)))
 (define (symbol-append . args)
   (string->symbol (apply string-append (map symbol->string args)))))

;; const-prop and const-fold adapted from 

(define-syntax (const-prop stx)
  (define (full-def datum)
    (match datum
      [`(const-prop ,node ,heap ,clos ,rlos ,primop)
       (let ([clos? (symbol-append clos '?)]
             [rlos? (symbol-append rlos '?)]
             [primop? (symbol-append primop '?)])
         (datum->syntax stx
                        `(let ([num-propped (box 0)])
                           ,(value-node?-proc 'n
                                              `(,clos? n)
                                              `(,rlos? n)
                                              `(,primop? n))
                           (define (bump-consts!)
                             (set-box! num-propped (add1 (unbox num-propped))))
                           (define (sav->prop-node sav loc)
                             (and sav
                                  (set? sav)
                                  (= 1 (set-count sav))
                                  (let ([av (set-first sav)])
                                    (cond [(value-node? av)
                                           (match av
                                             [(? ,clos? c)
                                              (cond [(∅? (,(symbol-append clos '-free) c))
                                                     (bump-consts!)
                                                     (,(symbol-append clos '-e) c)]
                                                    [else #f])]
                                             [(? ,rlos? r)
                                              (cond [(∅? (,(symbol-append rlos '-free) r))
                                                     (bump-consts!)
                                                     (,(symbol-append rlos '-e) r)]
                                                    [else #f])]
                                             [(? ,primop?) (bump-consts!) av]
                                             [(datum _ v) (bump-consts!) av]
                                             [(primr _ op) (bump-consts!) av]
                                             [(lam _ xs e)
                                              (cond [(∅? (free av)) (bump-consts!) av]
                                                    [else #f])]
                                             [(rlm _ xs ys e)
                                              (cond [(∅? (free av)) (bump-consts!) av]
                                                    [else #f])]
                                             [(? atomic?)
                                              (bump-consts!) (datum -1 av)]
                                             [_ #f])]
                                          [else #f]))))
                           (define (cprop node)
                             (match node
                               [(? value-node?) node]
                               [(var l x)
                                (define sav
                                  (if (hash? heap)
                                      (hash-ref heap x #f)
                                      (vector-ref heap x)))
                                (or (sav->prop-node sav x) node)]
                               [(app l left rs) (app l (cprop left) (map cprop rs))]
                               [(datum l v) node]
                               [(lrc l xs es e) (lrc l xs (map cprop es) (cprop e))]
                               [(lam l xs e) (lam l xs (cprop e))]
                               [(rlm l xs rest e) (rlm l xs rest (cprop e))]
                               [(ife l p t e) (ife l (cprop p) (cprop t) (cprop e))]
                               [(st! l x e) (ife l x (cprop e))]
                               [(lcc l x e) (lcc l x (cprop e))]
                               [(primr l op) (primr l op)]
                               [_ (displayln (format "unmatched node during folding: ~a" node))
                                  node]))
                           (let ([propped (cprop ,node)])
                             (begin0 (values propped (unbox num-propped))
                               (set-box! num-propped 0))))))]))
  (datum->syntax stx (full-def (syntax->datum stx))))

(define-syntax (const-fold stx)
  (define foldable-sps
    `((add1 . ,add1)
      (sub1 . ,sub1)
      (+ . ,+)
      (- . ,-)
      (* . ,*)
;      (/ . ,/)
      (= . ,=)
      (< . ,<)
      (> . ,>)
      (<= . ,<=)
      (>= . ,>=)
      (bitwise-and . ,bitwise-and)
      (bitwise-not . ,bitwise-not)
      (bitwise-ior . ,bitwise-ior)
      (bitwise-xor . ,bitwise-xor)
      (quotient . ,quotient)
      (remainder . ,remainder)
      (modulo . ,modulo)
      (numerator . ,numerator)
      (denominator . ,denominator)
      (make-rectangular . ,make-rectangular)
      (make-polar . ,make-polar)
      (real-part . ,real-part)
      (imag-part . ,imag-part)
      (magnitude . ,magnitude)
      (abs . ,abs)
      (min . ,min)
      (max . ,max)
      (gcd . ,gcd)
      (lcm . ,lcm)
      (expt . ,expt)
      (exp . ,exp)
      (round . ,round)
      (floor . ,floor)
      (ceiling . ,ceiling)
      (even? . ,even?)
      (odd? . ,odd?)
      (sqrt . ,sqrt)
      (atan . ,atan)
      (sin . ,sin)
      (cos . ,cos)
      (asin . ,asin)
      (acos . ,acos)
      (log . ,log)
      (fl+ . ,fl+)
      (fl* . ,fl*)
      (fl/ . ,fl/)
      (fl- . ,fl-)
      (fl= . ,fl=)
      (fl< . ,fl<)
      (fl> . ,fl>)
      (fl<= . ,fl<=)
      (fl>= . ,fl>=)
      (flmin . ,flmin)
      (flmax . ,flmax)
      (flabs . ,flabs)
      (flround . ,flround)
      (flceiling . ,flceiling)
      (flfloor . ,flfloor)
      (fltruncate . ,fltruncate)
      (flcos . ,flcos)
      (flsin . ,flsin)
      (fltan . ,fltan)
      (flasin . ,flasin)
      (flacos . ,flacos)
      (flatan . ,flatan)
      (fllog . ,fllog)
      (flexp . ,flexp)
      (flsqrt . ,flsqrt)
      (flexpt . ,flexpt)
      (->fl . ,->fl)
      (unsafe-fx= . ,unsafe-fx=)
      (unsafe-fx< . ,unsafe-fx<)
      (unsafe-fx> . ,unsafe-fx>)
      (unsafe-fx<= . ,unsafe-fx<=)
      (unsafe-fx>= . ,unsafe-fx>=)
      (unsafe-fx- . ,unsafe-fx-)
      (unsafe-fx+ . ,unsafe-fx+)
      (unsafe-fx* . ,unsafe-fx*)
      (unsafe-fxquotient . ,unsafe-fxquotient)
      (unsafe-fxremainder . ,unsafe-fxremainder)
      (unsafe-fxmodulo . ,unsafe-fxmodulo)
      (unsafe-fxabs . ,unsafe-fxabs)
      (unsafe-fxmin . ,unsafe-fxmin)
      (unsafe-fxmax . ,unsafe-fxmax)
      (unsafe-fxand . ,unsafe-fxand)
      (unsafe-fxxor . ,unsafe-fxxor)
      (unsafe-fxior . ,unsafe-fxior)
      (unsafe-fxnot . ,unsafe-fxnot)
      (unsafe-fxlshift . ,unsafe-fxlshift)
      (unsafe-fxrshift . ,unsafe-fxrshift)
      (number? . ,number?)
      (complex? . ,complex?)
      (integer? . ,integer?)
      (rational? . ,rational?)
      (fixnum? . ,fixnum?)
      (flonum? . ,flonum?)
      (real? . ,real?)
      (zero? . ,zero?)
      (exact? . ,exact?)
      (inexact? . ,inexact?)
      (exact->inexact . ,exact->inexact)
      (inexact->exact . ,inexact->exact)
      (positive? . ,positive?)
      (negative? . ,negative?)
      (inexact-real? . ,inexact-real?)
      (exact-integer? . ,exact-integer?)
      (exact-nonnegative-integer? . ,exact-nonnegative-integer?)
      (exact-positive-integer? . ,exact-positive-integer?)
      (equal? . ,equal?)
      (eqv? . ,eqv?)
      (eq? . ,eq?)
      (vector . ,vector)
      (vector-immutable . ,vector-immutable)
      (make-vector . ,make-vector)
      (vector-ref . ,vector-ref)
      (vector-set! . ,vector-set!)
      (vector-length . ,vector-length)
      (vector->list . ,vector->list)
      (list->vector . ,list->vector)
      (list? . ,list?)
      (length . ,length)
      (vector? . ,vector?)
      (string? . ,string?)
      (string->symbol . ,string->symbol)
      (string=? . ,string=?)
      (string>? . ,string>?)
      (string<? . ,string<?)
      (string>=? . ,string>=?)
      (string<=? . ,string<=?)
      (string-ci=? . ,string-ci=?)
      (string-ci>? . ,string-ci>?)
      (string-ci<? . ,string-ci<?)
      (string-ci>=? . ,string-ci>=?)
      (string-ci<=? . ,string-ci<=?)
      (string-append . ,string-append)
      (number->string . ,number->string)
      (char? . ,char?)
      (char=? . ,char=?)
      (char<? . ,char<?)
      (char>? . ,char>?)
      (char>=? . ,char>=?)
      (char<=? . ,char<=?)
      (char-ci=? . ,char-ci=?)
      (char-ci<? . ,char-ci<?)
      (char-ci>? . ,char-ci>?)
      (char-ci>=? . ,char-ci<=?)
      (char-alphabetic? . ,char-alphabetic?)
      (char-numeric? . ,char-numeric?)
      (char-whitespace? . ,char-whitespace?)
      (char-lower-case? . ,char-lower-case?)
      (char-upper-case? . ,char-upper-case?)
      (char->integer . ,char->integer)
      (integer->char . ,integer->char)
      (char-upcase . ,char-upcase)
      (char-downcase . ,char-downcase)
      (symbol? . ,symbol?)
      (symbol->string . ,symbol->string)
      (procedure? . ,procedure?)
      (not . ,not)
      (boolean? . ,boolean?)
      (cons . ,cons)
      (pair? . ,pair?)
      (null? . ,null?)))
  (define foldable (map car foldable-sps))
  (define (full-def datum)
    (match datum
      [`(const-fold ,node ,clos ,rlos ,primop)
       (let ([clos? (symbol-append clos '?)]
             [rlos? (symbol-append rlos '?)]
             [primop? (symbol-append primop '?)])
         `(let ([num-folded (box 0)])
            ,(list 'define 'foldable-sps `',foldable-sps)
            ,(list 'define 'foldable `',foldable)
            ,(value-node?-proc 'n `(,clos? n) `(,rlos? n) `(,primop? n))
            (define changed? #f)
            ;; fold-1 : ast.exp hash[symbol, value] ->
            ;;   value : or[literal, primop]
            (define (fold-1 node env)
              ;; llλ : list[var] list[exp] exp ->
              ;;       or[bool, hash[symbol, value]] hash[symbol, value]
              ;; this should be cleaner
              (define (llλ xs args body)
                (define (ext-when env x arg all-value?)
                  (define env* (and (value-node? arg) (hash-set env x arg)))
                  (values (and all-value? env*) (or env* env)))
                (for/fold ([all-val? #t] [env env])
                    ([x (in-list xs)] [arg (in-list args)])
                  (ext-when env x arg all-val?)))
              (define (bump-folded!)
                (set-box! num-folded (add1 (unbox num-folded)))
                (set! changed? #t))
              (define (maybe-get env x) (hash-ref env x #f))
              (define (fold-1* node) (fold-1 node env))
              (define (fold-1s nodes) (map (λ (node) (fold-1* node)) nodes))
              (match node
                [(? datum?) node]
                [(? ,clos?) node]
                [(? ,rlos?) node]
                [(? ,primop?) node]
                [(? primr?) node]
                [(var _ x)
                 (let ([bound? (hash-ref env x #f)])
                   (cond [bound? (bump-folded!) bound?]
                         [else node]))]
                [(ife _ (datum _ #f) _ e) (bump-folded!) (fold-1* e)]
                [(ife _ (? value-node?) t _) (bump-folded!) (fold-1* t)]
                [(ife l p t e) (ife l (fold-1* p) (fold-1* t) (fold-1* e))]
                [(st! l x e) (st! l x (fold-1* e))]
                [(app l (? primop? p) args)
                 (define op (,(symbol-append primop '-which) p))
                 (cond [(and (memv op foldable) (andmap value-node? args))
                        (define err (λ () (error 'fold-1 "unimplemented primop ~a" op)))
                        (define val (apply (dict-ref foldable-sps op err)
                                           (map (λ (arg) (if (datum? arg)
                                                             (datum-val arg)
                                                             arg))
                                                args)))
                        ;; atoms or data, nothing else so far
                        (bump-folded!)
                        (datum -1 val)]
                       [else (app l p (fold-1s args))])]
                [(app l (primr l1 op) args)
                 (cond [(and (memv op foldable) (andmap value-node? args))
                        (define err
                          (λ () (error 'fold-1 "unimplemented primop ~a" op)))
                        (define val (apply (dict-ref foldable-sps op err)
                                           (map (λ (arg) (if (datum? arg)
                                                             (datum-val arg)
                                                             arg))
                                                args)))
                        (bump-folded!)
                        (datum -1 val)]
                       [else (app l (primr l1 op) (fold-1s args))])]
                [(app l (? ,rlos? r) args)
                 #;(app l r (fold-1s args))
                 (define xs (,(symbol-append rlos '-x) r))
                 (define r (,(symbol-append rlos '-r) r))
                 (define e (,(symbol-append rlos '-e) r))
                 (define-values (rs-arg xs-args)
                   (split-at-right args (- (length args) (length xs))))
                 (define-values (all-val? env*)
                   (llλ (cons r xs) (cons rs-arg xs-args) e))
                 (cond [all-val? (bump-folded!) (fold-1 e env*)]
                       [else (app l r (fold-1s args))])]
                [(app l (? ,clos? c) args)
                 (define xs (,(symbol-append clos '-x) c))
                 (define e (,(symbol-append clos '-e) c))
                 (define-values (all-val? env*) (llλ xs args e))
                 (cond [all-val? (bump-folded!) (fold-1 e env*)]
                       [else (app l c (fold-1s args))])]
                [(app l (lam l1 xs e) args)
                 (define-values (all-val? env*) (llλ xs args e))
                 (cond [all-val? (bump-folded!) (fold-1 e env*)]
                       [else (app l (lam l1 xs (fold-1* e)) (fold-1s args))])]
                [(app l (rlm l1 xs rs e) args)
                 #;(app l (rlm l1 xs rs (fold-1* e)) (fold-1s args))
                 (define-values (rs-arg xs-args)
                   (split-at-right args (- (length args) (length xs))))
                 (define-values (all-val? env*)
                   (llλ (cons rs xs) (cons rs-arg xs-args) e))
                 (cond [all-val? (bump-folded!) (fold-1 e env*)]
                       [else (app l (rlm l1 xs rs (fold-1* e)) (fold-1s args))])]
                [(app l left args) (app l (fold-1* left) (fold-1s args))]
                [(lrc l xs es e)
                 (define-values (all-val? env*) (llλ xs es e))
                 (cond [all-val? (bump-folded!) (fold-1 e env*)]
                       [else (lrc l xs (fold-1s es) (fold-1* e))])]
                [(lam l xs e) (lam l xs (fold-1* e))]
                [(rlm l xs rs e) (rlm l xs rs (fold-1* e))]
                [(st! l x e) (st! l x (fold-1* e))]
                [(lcc l x e) (lcc l x (fold-1* e))]
                [null null]
                [_ (displayln (format "unmatched node during folding: ~a" node))
                   node]))
            (let fold-until-fixpt ([result (fold-1 ,node (hash))])
              (cond [changed?
                     (set! changed? #f)
                     (fold-until-fixpt (fold-1 result (hash)))]
                    [else (begin0 (values result (unbox num-folded))
                            (set-box! num-folded 0))]))))]))
  (datum->syntax stx (full-def (syntax->datum stx))))

;; takes the aval identifier
;; modify to allow passing output of aval as well
(define-syntax (make-prop-folder stx)
  (define (symbol-append . args)
    (string->symbol (apply string-append (map symbol->string args))))
  (define (full-def stx)
    (match (syntax->datum stx)
      [`(make-prop-folder ,name)
       (let ([box-name (symbol-append name '-box)]
             [prop-folder (symbol-append name '-prop-folder)]
             [clos (symbol-append name '-clos)]
             [rlos (symbol-append name '-rlos)]
             [primop (symbol-append name '-primop)])
         `(begin
            (define ,box-name (box #f))
            (define (,prop-folder file)
              (displayln (format "analyzing \"~a\"..." file))
              (define sexp
                (with-input-from-file file
                  (λ () (for/list ([form (in-port read)]) form))))
              (let-values ([(scm pcm heap ans) (with-limit-handler (,name sexp))])
                (displayln "analysis done, starting prop/fold loop")
                (define (loop ast [iterations 1] [total-propped 0] [total-folded 0])
                  (define-values (propped-ast num-propped)
                    (const-prop ast heap ,clos ,rlos ,primop))
                  (define-values (folded-ast num-folded)
                    (const-fold propped-ast ,clos ,rlos ,primop))
                  (if (zero? (+ num-propped num-folded))
                        (values iterations total-propped total-folded folded-ast)
                      (loop folded-ast
                            (add1 iterations)
                            (+ num-propped total-propped)
                            (+ num-folded total-folded))))
                (loop (unbox ,box-name))))))]))
  (datum->syntax stx (full-def stx)))

;; some of kcfa-instantiations.rkt is repeated here, with minor changes
;; what about boxes? pull out the prepare proc, provide, use instead of
;; boxing

(define-syntax-rule (with-concrete body)
  (splicing-syntax-parameterize
   ([widen (make-rename-transformer #'eval-widen)])
   body))

(define-syntax-rule (with-abstract . body)
  (splicing-syntax-parameterize
   ([widen (make-rename-transformer #'flatten-value)])
   . body))

;; strict pd
(mk-imperative/∆s^-fixpoint
  imperative/∆s-fixpoint/c imperative/∆s-ans/c?
  imperative/∆s-ans/c-v imperative/∆s-touches-0/c)(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-σ-∆s!
    (with-abstract
      (mk-analysis #:aval 0cfa^/∆s!
                   #:clos 0cfa^/∆s!-clos #:rlos 0cfa^/∆s!-rlos
                   #:primop 0cfa^/∆s!-primop
                   #:prepare (λ (sexp)
                                (let ([e (prepare-imperative parse-prog sexp)])
                                  (begin (set-box! 0cfa^/∆s!-box e) e)))
                   #:ans imperative/∆s-ans/c
                   #:touches imperative/∆s-touches-0/c
                   #:fixpoint imperative/∆s-fixpoint/c
                   #:global-σ #:wide))))))
(make-prop-folder 0cfa^/∆s!)
(define strict-pd-apf 0cfa^/∆s!-prop-folder)
(provide strict-pd-apf)

;; pd
(mk-imperative/∆s^-fixpoint
  imperative-lazy/∆s-fixpoint/c imperative-lazy/∆s-ans/c?
  imperative-lazy/∆s-ans/c-v imperative-lazy/∆s-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-σ-∆s!
    (with-abstract
      (mk-analysis #:aval lazy-0cfa^/∆s!
                   #:clos lazy-0cfa^/∆s!-clos #:rlos lazy-0cfa^/∆s!-rlos
                   #:primop lazy-0cfa^/∆s!-primop
                   #:prepare (λ (sexp)
                                (let ([e (prepare-imperative parse-prog sexp)])
                                  (begin (set-box! lazy-0cfa^/∆s!-box e) e)))
                   #:ans imperative-lazy/∆s-ans/c
                   #:touches imperative-lazy/∆s-touches-0/c
                   #:fixpoint imperative-lazy/∆s-fixpoint/c
                   #:global-σ #:wide))))))
(make-prop-folder lazy-0cfa^/∆s!)
(define pd-apf lazy-0cfa^/∆s!-prop-folder)
(provide pd-apf)

;; "pt"

(mk-prealloc/timestamp^-fixpoint prealloc/imperative-fixpoint/c prealloc-ans/c?
                                 prealloc-ans/c-v prealloc-touches-0/c)
(with-nonsparse
 (with-lazy
  (with-0-ctx/prealloc
   (with-prealloc/timestamp-store
    (with-mutable-worklist
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^/c/prealloc/timestamp!
                   #:clos lazy-0cfa^/c/prealloc/timestamp!-clos
                   #:rlos lazy-0cfa^/c/prealloc/timestamp!-rlos
                   #:primop lazy-0cfa^/c/prealloc/timestamp!-primop
                   #:prepare
                   (λ (sexp)
                      (let ([e (prepare-prealloc parse-prog sexp)])
                        (set-box! lazy-0cfa^/c/prealloc/timestamp!-box e) e))
                   #:ans prealloc-ans/c
                   #:touches prealloc-touches-0/c
                   #:fixpoint prealloc/imperative-fixpoint/c
                   #:global-σ #:wide)))))))
(make-prop-folder lazy-0cfa^/c/prealloc/timestamp!)
(provide lazy-0cfa^/c/prealloc/timestamp!)
(define pt-apf lazy-0cfa^/c/prealloc/timestamp!-prop-folder)
(provide pt-apf)


;Following up, yes, there is. After "pd" just change with-lazy to with-strict. If it finishes, turn off compilation and run constant folding. I proved compilation and store deltas precision-preserving, so we can use numbers from that as baseline. If that works, get the numbers, then get numbers using with-lazy, and finally timestamp approximation (pt). We just need you to run the benchmarks from the paper http://arxiv.org/abs/1211.3722

(define easy
  (map (λ (x) (string-append "../benchmarks/" x))
       '("fact.sch" "flatten.sch" "introspective.sch" "matt-gc.sch"
         "sergey/blur.sch" "sergey/kcfa2.sch" "sergey/kcfa3.sch" "sergey/sat.sch")))
(define paper
  (map (λ (x) (string-append "../benchmarks/toplas98/" x))
       '("boyer.sch" "../church.sch" "../earley.sch" "graphs.sch"
         "lattice.scm" "maze.sch" "matrix.scm" "../mbrotZ.sch" "nbody.sch"
         "nucleic.sch")))
(provide easy paper)

(define (run-prop-folders prop-folders files show-ast?)
  (define (run files)
    (map (λ (file)
            (cons file
                  (map (λ (name-apf)
                          (let-values ([(it np nf ast) (time ((cdr name-apf) file))])
                            (if show-ast?
                                (displayln (format "initial ast:~n~a~n" ast))
                                (void))
                            (displayln (format "fixpoint at iteration ~a" it))
                            (displayln (format "num propped: ~a" np))
                            (displayln (format " num folded: ~a" nf))
                            (if show-ast?
                                (displayln (format " folded-ast:~n~a" ast))
                                (void))
                            (displayln (format "done with ~a~n" file))
                            (list (car name-apf) it np nf ast)))
                       prop-folders)))
         files))
  (define out (run files))
  (define print
    (map (λ (l)
            (format "~a:~a"
                    (car l)
                    (foldr (λ (n a)
                              (format "~a~n  ~a: ~a ~a ~a"
                                      a
                                      (car n)
                                      (cadr n)
                                      (caddr n)
                                      (cadddr n)))
                           ""
                           (cdr l))))
         out))
  (for-each (λ (s) (displayln s)) print)
  #t)
(provide run-prop-folders)


(run-prop-folders `(,(cons "strict-pd" strict-pd-apf)
                    ,(cons "pd" pd-apf)
                    ,(cons "pt" pt-apf))
                  easy
                  false)

;; todo?: integrate into run-benchmark
