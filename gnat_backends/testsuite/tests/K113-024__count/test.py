from test_support import *

prove("count.adb",opt=["-P", "test.gpr", "--all-vcs"])
