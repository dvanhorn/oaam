#lang racket
(require (prefix-in church: "church-example.rkt")
	 "../code/ast.rkt")

(require (prefix-in wide: "../code/0cfa.rkt")
	 (prefix-in compile: "../code/0cfa-compile.rkt")
	 (prefix-in lazy: "../code/0cfa-lazy.rkt")
	 (prefix-in lazy+compile: "../code/0cfa-lazy-compile.rkt")
	 (prefix-in special: "../code/0cfa-specialize-lazy-compile.rkt")
	 (prefix-in delta: "../code/0cfa-delta.rkt"))

(define (enchilada p)
  (define P (parse p))
  (define (bench str fun)
    (printf "~a:~n   " str)
    (collect-garbage)
    (collect-garbage)
    (time (void (fun P)))
    (newline))


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

  (bench "Eval" wide:eval))

(require (prefix-in eta: "eta.rkt")
	 (prefix-in mj09: "midtgaard-jensen09.rkt")
	 (prefix-in blur: "blur.rkt"))

(enchilada eta:P)
(enchilada mj09:P)
(enchilada blur:P)
