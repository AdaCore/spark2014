from test_support import *

# GNATprove inlining enabled under -gnatdQ for now
prove_all(steps=10000, opt=["-cargs", "-gnatdQ"])
