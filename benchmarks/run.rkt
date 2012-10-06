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

(printf "0CFA style abstract^2 machine~n")
(printf "=============================~n~n")

(printf "Store polyvariance:~n   Forget it.~n~n")

(require (prefix-in wide: "../code/0cfa.rkt"))
(bench "Wide Store" wide:aval^)

(require (prefix-in compile: "../code/0cfa-compile.rkt"))
(bench "Compile" compile:aval^)

(require (prefix-in lazy: "../code/0cfa-lazy.rkt"))
(bench "Lazy" lazy:aval^)

(require (prefix-in lazy+compile: "../code/0cfa-lazy-compile.rkt"))
(bench "Compile + Lazy" lazy+compile:aval^)

(require (prefix-in special: "../code/0cfa-specialize-lazy-compile.rkt"))
(bench "Special + Compile + Lazy" special:aval^)

(require (prefix-in delta: "../code/0cfa-delta.rkt"))
(bench "Delta Store + Special + Compile + Lazy" delta:aval^)
