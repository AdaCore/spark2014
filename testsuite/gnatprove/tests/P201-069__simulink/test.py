from test_support import *

# No counter-examples as there are platform issues in biasdivide
prove_all(opt=["--no-counterexample"], codepeer=True)
