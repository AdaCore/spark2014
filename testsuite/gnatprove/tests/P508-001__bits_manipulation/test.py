from test_support import *

# Do not use Z3 which causes diffs between platforms
prove_all(opt=["--prover=cvc4,altergo"])
