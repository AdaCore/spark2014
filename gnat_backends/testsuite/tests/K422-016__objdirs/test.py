from test_support import *

prove("a.adb",opt=["-P", "test.gpr", "--all-vcs"])
