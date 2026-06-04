from test_support import prove_all

prove_all(
    prover=["coq"],
    opt=["--steps=1"],
    filter_output=".*Grammar extension",
)
prove_all(
    prover=["coq"],
    opt=["--steps=1"],
    filter_output=".*Grammar extension",
)
