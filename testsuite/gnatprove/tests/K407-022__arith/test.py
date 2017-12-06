from test_support import *

# CE disabled due to gaia/local diffs
prove_all(opt=["--pedantic"], codepeer=True, counterexample=False)
