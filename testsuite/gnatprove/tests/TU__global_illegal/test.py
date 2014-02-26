from test_support import *

gcc("global_illegal.ads")
gcc("global_illegal_2.adb")
prove_all(opt=["-u", "global_illegal_3.adb"])
