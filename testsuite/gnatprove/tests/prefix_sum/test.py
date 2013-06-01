from test_support import *

prove_all(steps=1, opt=["-u", "prefixsum.adb", "prefixsum_expanded.adb", "prefixsum_general.adb"])
