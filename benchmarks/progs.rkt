#lang racket
(provide (all-defined-out))
(require racket/runtime-path)

(define (read-all)
  (define o (read))
  (if (eof-object? o) 
      '()
      (cons o (read-all))))

(define-runtime-path |.| ".")
(define (read-prog f)
  (with-input-from-file (build-path |.| f)
    read-all))

(define church
  (read-prog "church.sch"))

(define blur
  (read-prog "blur.sch"))

(define vhm08
  (read-prog "vanhorn-mairson08.sch"))

(define sat
  (read-prog "sat.sch"))

(define mj09
  (read-prog "midtgaard-jensen09.sch"))

(define eta
  (read-prog "eta.sch"))
