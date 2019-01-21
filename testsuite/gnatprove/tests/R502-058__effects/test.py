from test_support import *

# This should prove
prove_all(opt=["-cargs", "-gnateDSNEAK_EFFECT=False"])
# This should not prove
prove_all(opt=["-cargs", "-gnateDSNEAK_EFFECT=True"])
