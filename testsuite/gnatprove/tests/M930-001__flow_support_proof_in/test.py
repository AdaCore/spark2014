from test_support import *

do_flow(opt=["-u", "proof_in_legal.adb"])
do_flow(opt=["-u", "proof_in_illegal.adb"])
do_flow(opt=["-u", "proof_in_illegal_2.adb"])
