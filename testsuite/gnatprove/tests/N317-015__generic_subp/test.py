from test_support import *

# GNATprove inlining enabled under -gnatdQ for now
prove_all(opt=["-cargs", "-gnatdQ"])
