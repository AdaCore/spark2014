from test_support import *

prove_all(opt=["--replay"])
prove_all(cache_allowed=False)
prove_all(cache_allowed=False,opt=["--replay"])
