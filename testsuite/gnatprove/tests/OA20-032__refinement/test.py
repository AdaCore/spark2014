from test_support import *
prove_all(prover=["cvc4", "altergo"], opt=["--no-axiom-guard", "--proof-warnings"])
