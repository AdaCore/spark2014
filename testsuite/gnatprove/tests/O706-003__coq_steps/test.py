from test_support import *

prove_all(prover=["coq"],opt=["-P", "test.gpr", "--steps=1"], filter_output=".*Grammar extension")
prove_all(prover=["coq"],opt=["-P", "test.gpr", "--steps=1"], filter_output=".*Grammar extension")
