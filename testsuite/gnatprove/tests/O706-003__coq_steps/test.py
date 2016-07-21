from test_support import *

prove_all(prover=["coq"],opt=["-P", "test.gpr", "--steps=1"])
prove_all(prover=["coq"],opt=["-P", "test.gpr", "--steps=1"])
