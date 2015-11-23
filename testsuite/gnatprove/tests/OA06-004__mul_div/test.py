from test_support import *

# Do not run with counterexamples, as on Darwin this takes too much time.
prove_all(steps = 240, counterexample=False)
