from test_support import *

gcc("initializes_illegal.adb")
gcc("initializes_illegal_2.ads")
gcc("initializes_illegal_3.ads")
prove_all(opt=["-u", "initializes_illegal_4.adb"])
gcc("initializes_illegal_5.adb")
prove_all(opt=["-u", "initializes_illegal_6.adb"])
