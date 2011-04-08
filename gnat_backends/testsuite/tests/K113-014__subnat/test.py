from test_support import *

prove("subnat.adb",opt=["-P", "test.gpr", "--all-vcs"])
