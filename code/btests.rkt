#lang racket

(require "parse.rkt" "kcfa-instantiations.rkt"
         racket/sandbox)

(define (sch->sexp file)
  (with-input-from-file file
    (λ () (for/list ([form (in-port read)]) form))))

(define (prep file) (sch->sexp file))

(define-syntax-rule (log-thread kind)
  (let ([lr (make-log-receiver (current-logger) kind)])
    (thread (λ () (let loop () (define vs (sync lr)) (write vs) (newline) (loop))))))

(define (print-values . vs) (for ([v vs]) (display v) (newline)))

(define-syntax-rule (test aval e)
  (parameterize ([current-logger (make-logger 'stuck-states)])
#;#;
    (log-thread 'info)
    (log-thread 'debug)
    (with-handlers ([exn:fail:resource?
                     (λ (e) (case (exn:fail:resource-resource e)
                              [(time) (dump-memory-stats) (printf "Timeout~%")]
                              [(memory) (printf "Exhausted memory~%")]))])
      (with-limits 3600 10240
                   (call-with-values
                       (λ () (begin0 (time (aval e))
                                     (void)#;
                                     (dump-memory-stats)))
                     print-values)))))

(define to-test
  (list "../benchmarks/church.sch"
        "../benchmarks/mbrotZ.sch"
        "../benchmarks/earley.sch"
        "../benchmarks/toplas98/boyer.sch"
        "../benchmarks/toplas98/graphs.sch"
        "../benchmarks/toplas98/lattice.scm"
        "../benchmarks/toplas98/matrix.scm"
        "../benchmarks/toplas98/maze.sch" ;; call/cc
        "../benchmarks/toplas98/nbody.sch"
        "../benchmarks/toplas98/nucleic.sch"
        ;;"../benchmarks/toplas98/splay.scm" ;; old match
        ;;"../benchmarks/toplas98/nucleic2.sch" ;; define-syntax
        ;;"../benchmarks/toplas98/handle.scm" ;; old match and defmacro
))

(for ([t to-test]) (test lazy-0cfa^/c! (prep t)))
(printf "~%~%==============BASELINE=============~%~%")
(for ([t to-test]) (test 0cfa^ (prep t)))

