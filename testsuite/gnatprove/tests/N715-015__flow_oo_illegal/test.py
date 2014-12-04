from test_support import *

prove_all(opt=["-u", "illegal_1.adb"])
prove_all(opt=["-u", "root.adb"])
prove_all(opt=["-u", "simple_illegal_with_contracts.adb"])
prove_all(opt=["-u", "simple_illegal_without_contracts.adb"])
