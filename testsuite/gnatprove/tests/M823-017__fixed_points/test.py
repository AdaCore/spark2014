from test_support import *
prove_all(opt=["-u","binary_fixed.adb"], steps=2000)
prove_all(opt=["-u","decimal_fixed.adb"], steps=2000)
prove_all(opt=["-u","dynamic_fixed.adb"])
prove_all(opt=["-u","unsupported.adb"])
