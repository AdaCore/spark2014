from test_support import *

# Counterexamples are disabled because splitting leads to too many subgoals
# and it eventually timeouts (note that counterexample now always try to split).
prove_all(counterexample=False)
