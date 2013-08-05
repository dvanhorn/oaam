#!/bin/bash
benchmark="../../paper/benchmark"
echo " " > $benchmark
# Make sure this is ((i = base-num; i < (base-num + run-num); i+=1))
# from ../drive-benchmarks.rkt
for ((i = 0; i < 5; i+=1))
do
	grep cpu `find . -name "*.time.$i" -print` >> $benchmark
	grep "State count" `find . -name "*.time.$i" -print` >> $benchmark
	grep "Point count" `find . -name "*.time.$i" -print` >> $benchmark
	grep "States/second" `find . -name "*.time.$i" -print` >> $benchmark
	grep Timeout `find . -name "*.time.$i" -print` >> $benchmark
	grep Exhaust `find . -name "*.time.$i" -print` >> $benchmark
	grep Peak `find . -name "*.mem.$i" -print` >> $benchmark
	grep Current `find . -name "*.mem.$i" -print` >> $benchmark
done

