from test_support import *

# do not split unproved VCs to avoid reaching the timeout
prove_all(steps=1, opt=["-u", "power_and_sum.adb", "--proof=no_split"])
