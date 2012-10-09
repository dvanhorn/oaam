#lang racket
;; Enumerated sets facility

;; Copyright (c) 2006 David Van Horn
;; Licensed under the Academic Free License version 3.0

;; <dvanhorn@cs.brandeis.edu>

;; This is an implementation of the enum-sets structure from Scheme 48.  

(provide define-enum-set-type enum-set->list enum-set-member? enum-set=? 
         enum-set-union enum-set-intersection enum-set-negation
         integer->enum-set enum-set->integer)
(require (lib "9.ss" "srfi")
         (lib "60.ss" "srfi"))

(define-record-type enum-set-type
  (make-enum-set-type type set-name set-predicate element-predicate 
                      set-size index->element element-index)
  enum-set-type?
  (type              est-type)
  (set-name          est-set-name)
  (set-predicate     est-set-predicate)
  (element-predicate est-element-predicate)
  (set-size          est-set-size)
  (index->element    est-index->element)
  (element-index     est-element-index))

(define-record-type enum-set (make-enum-set type sum) enum-set?
  (type enum-set-type)
  (sum  enum-set-sum))

(define (check-arg pred arg proc)
  (when (not (pred arg))
    (error (or (object-name proc) 'procedure)
           "expects argument satisfying ~a, but given ~a." 
           (or (object-name pred) proc)
           (or (object-name arg) arg))))

(define (enum-set->integer es)
  (check-arg enum-set? es enum-set->integer)
  (enum-set-sum es))

(define (integer->enum-set type sum)
  (check-arg enum-set-type? type integer->enum-set)
  ;; could also check that sum is within the valid range.
  (make-enum-set type sum))

(define (enum-set->list es)
  (let ((sum (enum-set-sum es))
        (index->element (est-index->element (enum-set-type es))))
    (let loop ((ls '()) (sum sum))
      (if (zero? sum)
          ls
          (let ((i (first-set-bit sum)))
            (loop (cons (index->element i) ls)
                  (bitwise-xor sum (ash 1 i))))))))

(define (enum-set-member? es elem)
  (check-arg 
   (est-element-predicate (enum-set-type es)) elem  enum-set-member?)
  (let ((i ((est-element-index (enum-set-type es)) elem)))
    (not (zero? (bitwise-and (enum-set-sum es) (ash 1 i))))))

(define (enum-set=? es1 es2)
  (check-arg enum-set? es1 enum-set=?)
  (check-arg (est-set-predicate (enum-set-type es1)) es2 enum-set=?)
  (= (enum-set-sum es1) (enum-set-sum es2)))

(define (enum-set-union es1 es2)
  (check-arg enum-set? es1 enum-set-union)
  (check-arg (est-set-predicate (enum-set-type es1)) es2 enum-set-union)
  (make-enum-set
   (enum-set-type es1)
   (bitwise-ior (enum-set-sum es1) (enum-set-sum es2))))

(define (enum-set-intersection es1 es2)
  (check-arg enum-set? es1 enum-set-intersection)
  (check-arg 
   (est-set-predicate (enum-set-type es1)) es2 enum-set-intersection)
  (make-enum-set
   (enum-set-type es1)
   (bitwise-and (enum-set-sum es1) (enum-set-sum es2))))

(define (enum-set-negation es)
  (check-arg enum-set? es enum-set-negation)
  (make-enum-set
   (enum-set-type es)
   (bitwise-xor (- (ash 1 (est-set-size (enum-set-type es))) 1)
                (enum-set-sum es))))

(define-syntax define-enum-set-type
  (syntax-rules ()
    ((define-enum-set-type set-syntax set-type 
       predicate 
       list->x-set 
       element-syntax 
       element-predicate 
       element-vector 
       element-index)
     (begin
       (define-record-type %set-type (%set-type) set-type?)
       
       (define (predicate x)
         (and (enum-set? x)
              (set-type? (est-type (enum-set-type x)))))
       
       (define set-type
         (make-enum-set-type
          (%set-type)
          'type predicate
          element-predicate
          (vector-length element-vector)
          (lambda (index) (vector-ref element-vector index))
          element-index))
       
       (define-syntax sum-elements
         (syntax-rules ()
           ((sum-elements elems (elem . rest))
            (sum-elements 
             ((ash 1 (element-index (element-syntax elem))) . elems) rest))
           ((apply-element-syntax elems ())
            (bitwise-ior . elems))))
       
       (define-syntax set-syntax
         (syntax-rules ()
           ((set-syntax . elems) 
            (make-enum-set set-type (sum-elements () elems)))))
       
       (define (list->x-set ls)
         (make-enum-set 
          set-type
          (apply bitwise-ior 
                 (map (lambda (element) (ash 1 (element-index element)))
                      ls))))))))



(struct a () #:transparent)
(struct b a () #:transparent)
(struct c a () #:transparent)
(define *b (b))
(define *c (c))
(define-enum-set-type borc type borc-set? list->borcset borco a? (vector *b *c) (lambda (x)
                                                                                 (if (eq? x *b) 0 1)))

                                                                                    
