from test_support import *
import os

# With both memcache and countexample active we get a crash,
# so when using cache switch counterexamples off.
if "cache" in os.environ:
    ce = False
else:
    ce = True

prove_all(counterexample=ce)
