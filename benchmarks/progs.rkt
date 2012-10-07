#lang racket
(provide (all-defined-out))

(define (read-prog)
  (read)) ;; FIXME : need to handle series of defs+exp

(define church
  (with-input-from-file "church.sch" read-prog))

(define blur
  (with-input-from-file "blur.sch" read-prog))
