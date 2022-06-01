from test_support import prove_all

# Objective of this test is to test -f option.
# We run gnatprove with cvc5, and then with alt-ergo in the second run with -f.
# All VCs in the second run should be either unproved or proved by alt-ergo,
# showing that the first run was not taken into account.

prove_all(prover=["cvc5"], check_counterexamples=False)
prove_all(prover=["altergo"], check_counterexamples=False, opt=["-f"], steps=10)
