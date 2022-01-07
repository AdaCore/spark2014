from test_support import prove_all

# This test is used to check that Coq still works in the presence of obj
# directory

prove_all(
    opt=["--prover=coq", "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"],
    steps=None,
    counterexample=False,
    filter_output=".*Grammar extension",
)
