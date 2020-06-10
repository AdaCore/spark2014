from test_support import *

# Do not use Z3, as the step limit fluctuates too much between platforms, thus
# making it impossible to share a common expected output when Z3 is used,
# especially since it makes the test outrun the timeout limit on Darwin.

# Do not use CVC4, which crashes on one VC on Darwin, the range check on line
# 65 column 37 of ng.adb

prove_all(prover=None, steps=3000, counterexample=False)
