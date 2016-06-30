This is a bag of scripts to produce SMTLIB benchmarks. You will probably
want to be on a Linux system for these to work.

1) create_benchmarks.sh

   This will run the testsuite in benchmark mode (using fake_cvc4 and
   fake_alt-ergo) and place the raw results in a sub-directory 'data',
   created here.

2) collate_benchmarks.py

   This will take the stuff from (1) and place it into a 'bench' directory
   with nicer names.

3) Makefile

   Use this to process all benchmarks from (2).

4) process_results.py

   Skeleton script to look at the results produced by (3). The example here
   will collect all benchmarks where CVC4 does not render a verdict but
   Alt-Ergo does.


A note on fake_cvc4:

   This script will now also squirrel away the original VCs in the
   directory ~spark_2014_benchmarks, along with a note on the step limited
   used. It can also differentiate between counter-example and regular VCs.
