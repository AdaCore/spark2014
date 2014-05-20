from test_support import *

prove_all(opt=["-u", "proof_in_legal.adb"])
prove_all(opt=["-u", "proof_in_illegal.adb"])
prove_all(opt=["-u", "proof_in_illegal_2.adb"])
