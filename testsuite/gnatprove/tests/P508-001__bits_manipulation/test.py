from test_support import *

# Do not use Z3 which causes diffs between platforms
prove_all(opt=["--why3-conf=why3.conf",
               "--prover=cvc4,cvc4_alt,altergo"])
