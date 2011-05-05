from test_support import *

prove("stacks.adb",opt=["-P", "test.gpr", "--all-vcs"])
