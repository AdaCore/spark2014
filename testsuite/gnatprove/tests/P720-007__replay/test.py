from test_support import *

contains_manual_proof = False

prove_all(opt=["--replay"])
prove_all(cache_allowed=False)
prove_all(cache_allowed=False,opt=["--replay"])
