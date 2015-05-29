from test_support import *

gcc("depends_illegal.ads",opt=["-c", "-gnatf"])
gcc("depends_illegal_2.adb",opt=["-c", "-gnatf"])
prove_all(opt=["-u", "depends_illegal_3.adb"])
prove_all(opt=["-u", "depends_illegal_4.adb"])
