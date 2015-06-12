from test_support import *

prove_all(opt=["-P", "test1.gpr", "-u", "t.adb"])
prove_all(opt=["-P", "test2.gpr", "-u", "t.adb"])
prove_all(opt=["-P", "test3.gpr", "-u", "t.adb"])

