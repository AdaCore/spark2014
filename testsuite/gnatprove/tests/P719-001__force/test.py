from test_support import *

# Objective of this test is to test -f option.
# We run gnatprove with cvc4, and then with alt-ergo in the second run with -f.
# All VCs in the second run should be either unproved or proved by alt-ergo,
# showing that the first run was not taken into account.

prove_all (prover=["cvc4"])
prove_all (prover=["altergo"], opt=["-f"], steps=10)
