from test_support import *

prove("odometer.adb",opt=["-P", "test.gpr", "--all-vcs"])
