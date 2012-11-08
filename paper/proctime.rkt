#lang racket
(require parser-tools/lex "data.rkt" (for-syntax "data.rkt"))
(provide timings cpu run gc)

;; Quick and dirty parser to reformat cpu/run time of benchmark output into
;; Map[benchmark,Map[algo,(Vector Vector[Number] Vector[Number] Vector[Number])]]

(define timings (make-hash))
;; Initialize the map.
(for ([file names])
  (define h (make-hash))
  (hash-set! timings file h)
  (for ([algo algos]) (hash-set! h algo
                                 (vector ;; cpu/run/gc times
                                  (make-vector (add1 (- end-run start-run)) 'unset)
                                  (make-vector (add1 (- end-run start-run)) 'unset)
                                  (make-vector (add1 (- end-run start-run)) 'unset)))))
(define (cpu v) (vector-ref v 0))
(define (run v) (vector-ref v 1))
(define (gc v) (vector-ref v 2))

(define-syntax (mk-lexer stx)
  (syntax-case stx ()
    [(_ lexname) #`(lexer #,@(for/list ([name (append algos names)])
                               #`[#,name #,name])
                          [(union "." "/" "time" "cpu" "run" "gc" "real" whitespace ":") (lexname input-port)]
                          [(repetition 1 +inf.0 numeric) (string->number lexeme)])]))
(define L (mk-lexer L))
;; ./NAME.ALGO.time.RUN:cpu time: NUMBER real time: NUMBER gc time: NUMBER
;; grep cpu `find . -name '*time*' -print`
(with-input-from-file "timings"
  (λ ()
     (for ([line (in-port read-line)])
       (define sp (open-input-string line))
       (define-values (file algo run# cput runt gct)
         (apply values (for/list ([i (in-range 6)]) (L sp))))
       (define algnums (hash-ref (hash-ref timings file) algo))
       (vector-set! (cpu algnums) (- run# start-run) cput)
       (vector-set! (run algnums) (- run# start-run) runt)
       (vector-set! (gc algnums) (- run# start-run) gct)
       (close-input-port sp))))
