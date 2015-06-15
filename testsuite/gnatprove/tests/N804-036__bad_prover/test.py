from test_support import *

# this test calls a prover which is correctly configured but whose execution
# gives an error (here: the prover executable doesn't exist). The intent is to
# test the output of gnatprove in this specific case

prove_all(opt=["--prover=plop", "--why3-conf=test.conf"])
