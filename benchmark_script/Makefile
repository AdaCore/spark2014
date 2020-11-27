.PHONY: benchmark vcfiles

BENCHDIR=bench

all: benchmark

benchmark: alt-ergo.json z3.json cvc4.json

alt-ergo.json: vcfiles
	./prover_stats.py -j 0 -t 10 --prover altergo -o altergo.json $(BENCHDIR)/altergo

cvc4.json: vcfiles
	./prover_stats.py -j 0 -t 10 --prover cvc4 -o cvc4.json $(BENCHDIR)/cvc4_16

z3.json: vcfiles
	./prover_stats.py -j 0 -t 10 --prover z3 -o z3.json $(BENCHDIR)/z3_gnatprove

vcfiles:
	./create_benchmarks.py ../testsuite/gnatprove $(BENCHDIR)
