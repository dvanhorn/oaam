#lang racket

(require "parse.rkt" "kcfa-instantiations.rkt"
         racket/trace)

(define (sch->sexp file)
  (with-input-from-file file
    (λ () (for/list ([form (in-port read)]) form))))

(define (prep file) (sch->sexp file))

#;#;#;#;#;
(time (lazy-0cfa^/c (prep "../benchmarks/church.sch")))
(time (lazy-eval^/c (prep "../benchmarks/church.sch")))
(time (lazy-0cfa∆/c (prep "../benchmarks/church.sch")))
(time (lazy-0cfa-gen^/c (prep "../benchmarks/church.sch")))
(time (lazy-0cfa-gen-σ-∆s^/c (prep "../benchmarks/church.sch")))
#;
(time (lazy-0cfa^/c! (prep! "../benchmarks/church.sch")))


(parameterize ([current-logger (make-logger 'stuck-states)])
  (define lr-stuck (make-log-receiver (current-logger) 'info))
  (define lr-debug (make-log-receiver (current-logger) 'debug))
  (thread (λ () (let loop () (define vs (sync lr-stuck)) (write vs) (newline) (loop))))
  (thread (λ () (let loop () (define vs (sync lr-debug)) (write vs) (newline) (loop))))
  (time (lazy-0cfa^/c! (prep "../benchmarks/toplas98/dynamic.sch"))))

#;#;#;#;#;#;#;#;#;
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/boyer.sch")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/graphs.sch")))
;; Uses defmacro
;;(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/handle.scm")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/lattice.scm")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/matrix.scm")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/maze.sch")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/nbody.sch")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/nucleic.sch")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/nucleic2.sch")))
(time (lazy-0cfa^/c! (prep! "../benchmarks/toplas98/splay.scm")))