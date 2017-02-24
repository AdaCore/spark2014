from test_support import *

# Do not use Z3, as the step limit fluctuates too much between platforms, thus
# making it impossible to share a common expected output when Z3 is used.
prove_all(prover=["cvc4","altergo"], steps=1000)
