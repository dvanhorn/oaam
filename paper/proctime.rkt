#lang racket
(require parser-tools/lex)
(provide timings (struct-out numbers))

(struct numbers (cpu run gc state-rate peak-mem current-mem states points timeout? exhaust?) #:transparent)

(module data racket/base
  (provide (all-defined-out))
  (define start-run 15)
  (define end-run 19)
  (define algos '("bl" "sp" "ls" "lc" "ld" "ia" "id" "pa" "pd" "it" "pt"))
  (define names '("church" "mbrotZ" "earley" "boyer" "graphs"
                  "lattice" "matrix" "maze" "nbody" "nucleic")))
(require 'data (for-syntax 'data))

;; Quick and dirty parser to reformat cpu/run time of benchmark output into
;; Map[benchmark,Map[algo,(Vector Vector[Number] Vector[Number] Vector[Number])]]

(define timings (make-hash))
;; Initialize the map.
(for ([file names])
  (define h (make-hash))
  (define runs (add1 (- end-run start-run)))
  (hash-set! timings file h)
  (for ([algo algos])
    (hash-set! h algo
               (apply numbers (build-list 10 (λ _ (make-vector runs 'unset)))))))

(define-syntax (mk-lexer stx)
  (syntax-case stx ()
    [(_ lexname) #`(lexer #,@(for/list ([name (append algos names)])
                               #`[#,name #,name])
                          ["cpu" 'cpu]
                          ["States/second" 'rate]
                          ["Point count" 'points]
                          ["State count" 'states]
                          ["Peak memory use after a collection" 'peak]
                          ["Result: Timeout" 'timeout]
                          ["Result: Exhausted memory" 'exhaust]
                          ["Current memory use" 'current]
                          [(union (repetition 1 +inf.0 numeric)
                                  (concatenation (repetition 1 +inf.0 numeric) "."
                                                  (repetition 1 +inf.0 numeric)))
                           (string->number lexeme)]
                          [(union "." "/"  "\"" "real" "gc"
                                  "time" "mem"
                                  whitespace ":") (lexname input-port)])]))

(define L (mk-lexer L))
;; ./out.sh
(with-input-from-file "benchmark"
  (λ ()
     (for ([line (in-port read-line)]
           #:unless (string=? "" (trim line)))
       (define sp (open-input-string line))
       (define-values (file algo run#)
         (apply values (for/list ([i (in-range 3)]) (L sp))))
       (define idx (- run# start-run))
       (match-define
        (numbers cpu real gc state-rate peak-mem current-mem states points timeout? exhaust?)
        (hash-ref (hash-ref timings file) algo))
       (case (L sp)
;; ./NAME.ALGO.time.RUN:cpu time: NUMBER real time: NUMBER gc time: NUMBER
         [(cpu) ;; Next three lexemes are numbers for cpu/real/gc times
          (vector-set! cpu idx (L sp))
          (vector-set! real idx (L sp))
          (vector-set! gc idx (L sp))]
;; ./NAME.ALGO.time.RUN:"States/second: NUMBER"
         [(rate) (vector-set! state-rate idx (L sp))]
;; ./NAME.ALGO.time.RUN:Timeout
         [(timeout)
          (vector-set! timeout? idx #t)
          (vector-set! exhaust? idx #f)]
;; ./NAME.ALGO.time.RUN:Exhausted Memory
         [(exhaust)
          (vector-set! timeout? idx #f)
          (vector-set! exhaust? idx #t)]
         [(peak) (vector-set! peak-mem idx (L sp))]
         [(current) (vector-set! current-mem idx (L sp))]
;; ./NAME.ALGO.time.RUN:"State count: NUMBER"
         [(states) (vector-set! states idx (L sp))]
;; ./NAME.ALGO.time.RUN:"Point count: NUMBER"
         [(points) (vector-set! points idx (L sp))]
         [else (printf "Whaaaat?~%")])
       (close-input-port sp))))
