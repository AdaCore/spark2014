from test_support import *

prove("qack.adb",opt=["-P", "test.gpr", "--all-vcs"])

