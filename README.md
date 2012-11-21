oaam
====

Optimizing Abstract^2 Machines

Requires Racket version 5.2 or higher (maybe the nightly)

To make the benchmark harness and all instantiations of
the algorithms/abstractions, run

raco make code/run-benchmark.rkt

To run benchmarks,

racket code/drive-benchmarks.rkt

Instructions for modification (times to run, how many threads, etc) are inline.

After benchmarks produce their output, run [code/bench/out.sh]
to produce [paper/benchmark].
Then, in [paper/], run

make getbib ; make bibtex ; make ; make

This will fetch the bibliography info, compile the bibliography,
build the paper and the charts using the produced numbers,
then rebuild the paper to correct references.

[paper/proctime.rkt] is the module that parses [paper/benchmark] and builds 
a hash table of raw numbers called timings, if you want to inspect more.