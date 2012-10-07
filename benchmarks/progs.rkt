#lang racket
(provide (all-defined-out))

(define (read-prog f)
  (with-input-from-file f
    read)) ;; FIXME : need to handle series of defs+exp

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