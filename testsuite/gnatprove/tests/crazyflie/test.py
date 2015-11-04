from test_support import *

# Do not include Z3 in list of provers due to runtime differences with steps
# on different platforms.
prove_all(opt=["-XMODE=Analyze","--prover=cvc4,altergo"],steps=5000)
