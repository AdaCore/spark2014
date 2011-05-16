from test_support import *

prove("anontype.adb",opt=["-P", "test.gpr", "--all-vcs"])
