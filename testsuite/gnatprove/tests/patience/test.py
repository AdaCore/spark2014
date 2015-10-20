from test_support import *

# Do not use Z3, as the step limit fluctuates too much between platforms, thus
# making it impossible to share a common expected output when Z3 is used.
prove_all_no_counterexample(opt=["--prover=cvc4,altergo"], steps=3000)
