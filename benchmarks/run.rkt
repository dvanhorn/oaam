#lang racket
(require (prefix-in church: "church-example.rkt")
	 "../code/ast.rkt")

(define P (parse church:P))
(define (bench str fun)
  (printf "~a:~n   " str)
  (collect-garbage)
  (collect-garbage)
  (time (void (fun P)))
  (newline))

(require (prefix-in wide: "../code/0cfa.rkt"))
(require (prefix-in compile: "../code/0cfa-compile.rkt"))
(require (prefix-in lazy: "../code/0cfa-lazy.rkt"))
(require (prefix-in lazy+compile: "../code/0cfa-lazy-compile.rkt"))
(require (prefix-in special: "../code/0cfa-specialize-lazy-compile.rkt"))
(require (prefix-in delta: "../code/0cfa-delta.rkt"))

(printf "0CFA style abstract^2 machine~n")
(printf "=============================~n~n")

(printf "Store polyvariance:~n   Forget it.~n~n")
(bench "Wide Store" wide:aval^)
(bench "Compile" compile:aval^)
(bench "Lazy" lazy:aval^)
(bench "Compile + Lazy" lazy+compile:aval^)
(bench "Special + Compile + Lazy" special:aval^)
(bench "Delta Store + Special + Compile + Lazy" delta:aval^)

(printf "Concrete interpretation~n")
(printf "=======================~n~n")

(bench "Eval" wide:eval)