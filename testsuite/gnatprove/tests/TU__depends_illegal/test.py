from test_support import *

gcc("depends_illegal.ads")
gcc("depends_illegal_2.adb")
prove_all(opt=["-u", "depends_illegal_3.adb"])
prove_all(opt=["-u", "depends_illegal_4.adb"])
