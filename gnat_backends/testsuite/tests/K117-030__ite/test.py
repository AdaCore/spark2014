from test_support import *

prove("ite.adb",opt=["-P", "test.gpr", "--all-vcs"])
