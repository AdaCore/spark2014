from test_support import *

gcc("initial_condition_illegal.adb")
prove_all(opt=["-u", "initial_condition_illegal_2.adb"])
prove_all(opt=["-u", "initial_condition_illegal_3.adb"])
prove_all(opt=["-u", "initial_condition_illegal_4.adb"])
