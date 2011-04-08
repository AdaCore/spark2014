from test_support import *

prove("inrange.adb",opt=["-P", "test.gpr", "--all-vcs"])
