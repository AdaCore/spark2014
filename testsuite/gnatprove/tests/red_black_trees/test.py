from test_support import *

prove_all(opt=["--no-axiom-guard",
               "--no-counterexample"],
          steps=50,
          prover=["cvc4"])
