from test_support import *

prove("max.adb",opt=["-P", "test.gpr", "--all-vcs"])
