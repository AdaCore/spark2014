from test_support import *

prove("s.adb",opt=["-P", "test.gpr", "--all-vcs"])
