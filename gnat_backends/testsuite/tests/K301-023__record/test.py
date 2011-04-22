from test_support import *

prove("rec.adb",opt=["-P", "test.gpr", "--all-vcs"])
