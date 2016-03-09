from test_support import *

prove_all(opt=["-P", "test.gpr","--prover=nonexisting_prover"], cache_allowed=False)
