from test_support import *

prove("main.adb",opt=["-P", "test.gpr", "--all-vcs"])

