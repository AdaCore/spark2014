from test_support import *

prove("glob.adb",opt=["-P", "test.gpr", "--all-vcs"])
