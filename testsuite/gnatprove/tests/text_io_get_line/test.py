from test_support import prove_all

# Do not run with Z3 (P212-018) until deterministic on all platforms
prove_all(
    opt=["--proof=progressive", "--function-sandboxing=off", "--counterexamples=off"],
    prover=["cvc5", "altergo"],
    steps=1500,
)
