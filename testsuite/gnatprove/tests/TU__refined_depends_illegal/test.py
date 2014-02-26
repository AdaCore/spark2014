from test_support import *

gcc("refined_depends_illegal.adb")
prove_all(opt=["-u", "refined_depends_illegal_2.adb"])
