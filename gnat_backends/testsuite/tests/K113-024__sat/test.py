from test_support import *

prove("sat.adb",opt=["-P", "test.gpr", "--all-vcs"])
