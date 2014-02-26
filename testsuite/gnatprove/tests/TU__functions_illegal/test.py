from test_support import *

gcc("functions_illegal.adb")
prove_all(opt=["-u", "functions_illegal_2.adb"])
