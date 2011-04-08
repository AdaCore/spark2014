from test_support import *

prove("find.adb",opt=["-P", "test.gpr", "--all-vcs"])
