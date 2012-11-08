#lang racket
(require parser-tools/lex "data.rkt" (for-syntax "data.rkt"))
(provide memusage)

;; Quick and dirty parser to reformat memory usage of benchmark output into
;; Map[benchmark,Map[algo,Vector[Number]]]

(define memusage (make-hash))
;; Initialize the map.
(for ([file names])
  (define h (make-hash))
  (hash-set! memusage file h)
  (for ([algo algos])
    (hash-set! h algo (make-vector (add1 (- end-run start-run))))))

(define-syntax (mk-lexer stx)
  (syntax-case stx ()
    [(_ lexname) #`(lexer #,@(for/list ([name (append algos names)])
                               #`[#,name #,name])
                          [(union "." "/" "mem"
                                  "Peak memory use after a collection"
                                  "Current memory use" whitespace ":") (lexname input-port)]
                          [(repetition 1 +inf.0 numeric) (string->number lexeme)])]))
(define L (mk-lexer L))
;; ./NAME.ALGO.mem.RUN:Current memory use: NUMBER
;; ./NAME.ALGO.mem.RUN:Peak memory use after a collection: NUMBER
(define (max-mem)
  (for ([line (in-port read-line)])
    (define sp (open-input-string line))
    (define-values (file algo run mem)
      (apply values (for/list ([i (in-range 4)]) (L sp))))
    (define bench (hash-ref memusage file (λ () (error 'hash-ref "File unset ~a" file))))
    (define algnums (hash-ref bench algo (λ () (error 'hash-ref "Algo unset ~a" algo))))
    (vector-set! algnums (- run start-run)
                 (max mem (vector-ref algnums (- run start-run))))
    (close-input-port sp)))
;; grep Peak `find . -name '*mem*' -print`
(with-input-from-file "peakmem" max-mem)
;; grep Current `find . -name '*mem*' -print`
(with-input-from-file "finalmem" max-mem)
