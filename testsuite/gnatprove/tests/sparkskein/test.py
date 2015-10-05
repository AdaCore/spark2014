from test_support import *

# Only unproved check is index check at line 266, proved by CVC4 with
# 100.000 steps currently. This is notoriously high, and might be related
# to the issue with CVC4 reported in O525-023. Moreover, this is proved on
# developer setup, but not in nightly testing. To be investigated under
# O612-012.

# All other checks are proved:
# . CVC4 proves all other checks except 2
# . Alt-Ergo and Z3 each prove one remaining check

# Do not use Z3, as the step limit fluctuates too much between platforms, thus
# making it impossible to share a common expected output when Z3 is used.

prove_all(opt=["--prover=cvc4,altergo"],procs=4,steps=1000)
