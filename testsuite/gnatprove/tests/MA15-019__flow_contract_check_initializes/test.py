from test_support import *

prove_all(opt=["-u", "init.adb"])
prove_all(opt=["-u", "init_2.ads"])
prove_all(opt=["-u", "initializes_legal.adb"])
prove_all(opt=["-u", "initializes_illegal.adb"])
prove_all(opt=["-u", "initializes_illegal_2.adb"])
prove_all(opt=["-u", "initializes_illegal_3.ads"])
