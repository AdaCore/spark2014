from test_support import *

prove("pack.adb",opt=["-P", "test.gpr", "--all-vcs"])
