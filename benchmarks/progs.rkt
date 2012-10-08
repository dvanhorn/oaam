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

(define vhm08
  (read-prog "vanhorn-mairson08.sch"))

(define mj09
  (read-prog "sergey/mj09.sch"))

(define eta
  (read-prog "sergey/eta.sch"))

(define kcfa2
  (read-prog "sergey/kcfa2.sch"))

(define kcfa3
  (read-prog "sergey/kcfa3.sch"))

(define blur
  (read-prog "sergey/blur.sch"))

(define loop2
  (read-prog "sergey/loop2.sch"))

(define sat
  (read-prog "sergey/sat.sch"))



