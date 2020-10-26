from test_support import *
# Do not use Z3, as the step limit fluctuates too much between platforms, thus
# making it impossible to share a common expected output when Z3 is used.
prove_all(steps=400, prover=["cvc4","altergo"])
check_output_file()
