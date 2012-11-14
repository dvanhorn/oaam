#lang racket
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generate numbers tabular (Program, LOC, Time (ms), Space (mb), Speed (states/sec)
(require (submod "../code/drive-benchmarks.rkt" data) "proctime.rkt")

(define (file->name s)
  (define path (string->path s))
  (define-values (base filename dir?) (split-path path))
  (path->string (path-replace-suffix filename "")))
(define (loc f)
  (with-input-from-file f
    (λ ()
       (for/sum ([l (in-port read-line)]) #:break (eq? l 'eof) 1))))
(define (entry name fn conv n)
  (match (average (fn n))
    [#f (cond [(vector-ref (numbers-timeout? n) 0)
               "\\text{{\\small $t$}}"]
              [(vector-ref (numbers-exhaust? n) 0)
               "\\text{{\\small $m$}}"]
              [else (error 'bench-overview "No numbers, timeout or oom!: ~a" name)])]
    [n (conv n)]))

(define (byte->mib b) (/ b (* 1024 1024)))
(define (nfigs n)
  (compose number->string
           (cond [(zero? n) (compose inexact->exact round)]
                 [else 
                  (define factor (expt 10 n))
                  (λ (x)
                     (if (integer? x)
                         x
                         (exact->inexact (/ (round (* factor x)) factor))))])))

(define ((suffixed-number figs) n)
  (define num-zeros (truncate (/ (log n) (log 10))))
  (define (order k suff)
    (and (>= num-zeros k)
         (format "~a~a" ((nfigs figs) (/ n (expt 10 k))) suff)))
  (or (order 9 "G")
      (order 6 "M")
      (order 3 "K")
      ((nfigs figs) n)))


(define files (list nucleic matrix nbody earley maze church lattice boyer mbrotZ))
(define comparisons (list numbers-run numbers-peak-mem numbers-state-rate))
(define conversions (list (compose (suffixed-number 1)  (λ (x) (/ x 1000)))
                          (compose (nfigs 0) byte->mib)
                          (suffixed-number 0)))
(define algos (list "sp" "pd"))

(define-syntax-rule (for/append guards body ...)
  (for/fold ([acc '()]) guards (let ([r (let () body ...)]) (append acc r))))

(with-output-to-file "bench-overview.tex" #:mode 'text #:exists 'replace
  (λ ()
     (printf "\\begin{tabular}{@{}l|r|r|r|r|r|r|r@{}}~%")
     (printf "Program & LOC~%")
     (printf "& \\multicolumn{2}{c|}{Time {\\small (s)}}~%")
     (printf "& \\multicolumn{2}{c|}{Space {\\small (MB)}}~%")
     (printf "& \\multicolumn{2}{c@{}}{Speed {\\small (state/s)}}~%")
     (printf "\\\\~%")
     (printf "\\hline\\hline~%")
     (printf
      (string-join
       (for/list ([file files])
         (define name (file->name file))
         (define numbers (hash-ref timings name))
         (format "~a & ~a & ~a"
                 name
                 (loc file)
                 (string-join
                  (for/append ([fn comparisons]
                               [conversion conversions])
                    (for/list ([algo algos])
                      (entry `(,name ,algo) fn conversion (hash-ref numbers algo))))
                  " & ")))
       " \\\\~%"))
     (printf "~%\\end{tabular}~%")))