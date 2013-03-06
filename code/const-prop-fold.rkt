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
      (or (datum? ,n) (atomic? ,n) (primr? ,n) (lam? ,n) (rlm? ,n) ,@pred-apps)))
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
                                (define sav (hash-ref heap x #f))
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
      (/ . ,/)
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
      (qvector^ . ,qvector^)
      (make-vector . ,make-vector)
      (vector-ref . ,vector-ref)
      (vector-set! . ,vector-set!)
      (vector-length . ,vector-length)
      (vector->list . ,vector->list)
      (list->vector . ,list->vector)
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
      (void? . ,void?)
      (void . ,void)
      (error . ,error)
      (not . ,not)
      (boolean? . ,boolean?)
      (cons . ,cons)
      (pair? . ,pair?)
      (null? . ,null?)
      (car . ,car)
      (cdr . ,cdr)))
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
                                           (map datum-val args)))
                        ;; assumes all arguments are datum for primops, which is not
                        ;; entirely true...
                        (bump-folded!)
                        (datum -1 val)]
                       [else (app l p (fold-1s args))])]
                [(app l (primr l1 op) args)
                 (cond [(and (memv op foldable) (andmap value-node? args))
                        (define err (λ () (error 'fold-1 "unimplemented primop ~a" op)))
                        (define val (apply (dict-ref foldable-sps op err)
                                           (map datum-val args)))
                        (bump-folded!)
                        (datum -1 val)]
                       [else (app l (primr l1 op) (fold-1s args))])]
                [(app l (? ,rlos? r) args)
                 (define xs (,(symbol-append rlos '-x) r))
                 (define r (,(symbol-append rlos '-r) r))
                 (define e (,(symbol-append rlos '-e) r))
                 (define-values (rs-arg xs-args) (split-at-right (length r) args))
                 (define-values (all-val? env*)
                   (llλ `(,r . ,xs) `(,rs-arg . ,xs-args) e))
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
                 (define-values (rs-arg xs-args) (split-at-right (length rs) args))
                 (define-values (all-val? env*)
                   (llλ `(,rs . ,xs) `(,rs-arg . ,xs-args) e))
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

(mk-set-fixpoint^ fix baseline-fixpoint baseline-ans?)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval baseline #:ans baseline-ans
                   #:clos baseline-clos #:rlos baseline-rlos
                   #:primop baseline-primop
                   #:fixpoint baseline-fixpoint
                   #:prepare (λ (sexp)
                                (let ([e (prepare-prealloc parse-prog sexp)])
                                  (begin (set-box! baseline-box e) e)))
                   #:σ-passing #:wide #:set-monad)))))))
(make-prop-folder baseline)
(provide baseline-prop-folder)

(mk-special-set-fixpoint^ fix 0cfa-set-fixpoint^ 0cfa-ans^?)
(with-nonsparse
 (with-strict
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval 0cfa^ #:ans 0cfa-ans^
                   #:clos 0cfa^-clos #:rlos 0cfa^-rlos
                   #:primop 0cfa^-primop
                   #:fixpoint 0cfa-set-fixpoint^
                   #:prepare (λ (sexp)
                                (let ([e (prepare-prealloc parse-prog sexp)])
                                  (begin (set-box! 0cfa^-box e) e)))
                   #:σ-passing #:wide #:set-monad)))))))
(make-prop-folder 0cfa^)
(provide 0cfa^-prop-folder)

(mk-special-set-fixpoint^ fix lazy-0cfa-set-fixpoint^ lazy-0cfa-ans^?)
(with-nonsparse
 (with-lazy
  (with-0-ctx
   (with-whole-σ
    (with-σ-passing-set-monad
     (with-abstract
      (mk-analysis #:aval lazy-0cfa^ #:ans lazy-0cfa-ans^
                   #:clos lazy-0cfa^-clos #:rlos lazy-0cfa^-rlos
                   #:primop lazy-0cfa^-primop
                   #:prepare (λ (sexp)
                                (let ([e (prepare-prealloc parse-prog sexp)])
                                  (begin (set-box! lazy-0cfa^-box e) e)))
                   #:fixpoint lazy-0cfa-set-fixpoint^
                   #:σ-passing #:wide #:set-monad)))))))
(make-prop-folder lazy-0cfa^)
(provide lazy-0cfa^-prop-folder)

(mk-imperative/∆s^-fixpoint
                imperative/∆s-fixpoint/c imperative/∆s-ans/c?
                imperative/∆s-ans/c-v imperative/∆s-touches-0/c)
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
                   #:ans imperative/∆s-ans/c
                   #:touches imperative/∆s-touches-0/c
                   #:fixpoint imperative/∆s-fixpoint/c
                   #:global-σ #:wide))))))
(make-prop-folder lazy-0cfa^/∆s!)
(provide lazy-0cfa^/∆s!-prop-folder)

(define easy
  (map (λ (x) (string-append "../benchmarks/" x))
       '("church.sch" "earley.sch" "fact.sch" "flatten.sch"
         "introspective.sch" "matt-gc.sch" "sergey/blur.sch"
         "sergey/eta.sch" "sergey/kcfa2.sch"
         "sergey/kcfa3.sch" "sergey/sat.sch")))
(define paper
  (map (λ (x) (string-append "../benchmarks/toplas98/"))
       '("boyer.sch" "dynamic.sch" "graphs.sch" "lattice.scm" "maze.sch"
         "matrix.scm" "nbody.sch" "nucleic.sch"
       #;(these don't seem to aval correctly: "handle.scm" "nucleic2.sch" "splay.scm"))))
(provide easy paper)

(define (run-prop-folders prop-folders files)
  (define (run files)
    (map (λ (apf) (map (λ (file)
                          (displayln "")
                          (let-values ([(it np nf ast) (time (apf file))])
                            (displayln (format "fixpoint at iteration ~a" it))
                            (displayln (format "num propped: ~a" np))
                            (displayln (format " num folded: ~a" nf))
                            (displayln (format " folded-ast:~n~a" ast))
                            (list it np nf ast)))
                       files))
         prop-folders))
  (run files))
(provide run-prop-folders)

#;
(run-prop-folders `(,baseline-prop-folder
                    ,0cfa^-prop-folder
                    ,lazy-0cfa^-prop-folder
                    ,lazy-0cfa^/∆s!-prop-folder)
                  (append easy paper))

;; todo?: integrate into run-benchmark
