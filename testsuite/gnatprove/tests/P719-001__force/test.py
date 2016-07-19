from test_support import *

# Objective of this test is to test -f option.
# the test contains a VC that alt-ergo with low steps can not prove. We let the first run prove
# everything, and then run with only alt-ergo and option -f. That VC should
# not be proved in the second run, showing that the results of the first are
# not taken into account.

prove_all (prover=["cvc4"])
prove_all (prover=["altergo"], opt=["-f"], steps=10)
