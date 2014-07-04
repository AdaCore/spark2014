from test_support import *
import glob

prove_all(opt=["--prover=cvc4"], steps=1, vc_timeout=1)
