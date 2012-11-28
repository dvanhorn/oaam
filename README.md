Optimizing Abstract Abstract Machines
=====================================

Authors: [J. Ian Johnson](http://www.ccs.neu.edu/home/ianj/),
[Matthew Might](http://matt.might.net/), 
[David Van Horn](http://www.ccs.neu.edu/home/dvanhorn/)

Overview
--------

Abstracting abstract machines is a lightweight approach to designing
sound and computable program analyses. Although sound analyzers are
straightforward to build under this approach, they are also
prohibitively inefficient.

This repository contributes a step-by-step process for going from a
naive analyzer derived under the abstracting abstract machine approach
to an efficient program analyzer. The end result of the process is a
two to three order-of-magnitude improvement over the systematically
derived analyzer, making it competitive with hand-optimized
implementations that compute fundamentally less precise results.

The repository contains a paper describing the approach and
summarizing the results of an empirical evalution; an implementation
of a framework of analyses that can be instantiated to each step of
the optimizations; and a benchmark suite and harness that evaluates
each optimization.

Paper
-----

The paper _Optimizing Abstract Abstract Machines_ is available as a
PDF from [arXiv.org](http://arxiv.org/abs/1211.3722).

Building
--------

Requires [Racket](http://www.racket-lang.org/) version 5.2 or higher
(maybe the nightly)

### Running benchmarks

To make the benchmark harness and all instantiations of
the algorithms/abstractions, run

    raco make code/run-benchmark.rkt

(This may take several minutes due to the substantial compile-time
computation involved.)

To run benchmarks,

    racket code/drive-benchmarks.rkt

(This may take several hours.)

Instructions for modification (times to run, how many threads, etc)
are inline.

### Building the paper

After benchmarks produce their output, run [code/bench/out.sh] to
produce [paper/benchmark].  Then, in [paper/], run

    make getbib ; make bibtex ; make ; make

This will fetch the bibliography info, compile the bibliography, build
the paper and the charts using the produced numbers, then rebuild the
paper to correct references.

[paper/proctime.rkt] is the module that parses [paper/benchmark] and
builds a hash table of raw numbers called timings, if you want to
inspect more.