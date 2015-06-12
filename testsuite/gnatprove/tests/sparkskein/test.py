from test_support import *

# Only unproved check is index check at line 266, proved by CVC4 with
# 100.000 steps currently. This is notoriously high, and might be related
# to the issue with CVC4 reported in O525-023. Moreover, this is proved on
# developer setup, but not in nightly testing. To be investigated under
# O612-012.

# All other checks are proved:
# . CVC4 proves all other checks expect 2
# . Alt-Ergo and Z3 each prove one remaining check

prove_all(opt=["--prover=cvc4,altergo,z3"],procs=4)
