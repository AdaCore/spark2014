from test_support import *

prove_all(opt=["-u", "const.adb"])
prove_all(opt=["-u", "const2.adb"])
prove_all(opt=["-u", "const3.adb"])
prove_all(opt=["-u", "const4.adb"])
prove_all(opt=["-u", "other.adb"])
