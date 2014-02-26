from test_support import *

gcc("refined_global_illegal.adb")
prove_all(opt=["-u", "refined_global_illegal_2.adb"])

