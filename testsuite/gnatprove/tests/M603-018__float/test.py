from test_support import *

# Disable Z3 until we fix the platform issues
prove_all(opt=["--prover=cvc4,altergo"])
