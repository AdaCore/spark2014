from test_support import *
prove_all(steps=30000, opt=["--no-axiom-guard"], prover=["z3"], no_fail=True)
