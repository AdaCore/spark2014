from test_support import *

prove("ar.adb",opt=["-P", "test.gpr", "--all-vcs"])
