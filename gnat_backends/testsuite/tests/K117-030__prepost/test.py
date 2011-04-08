from test_support import *

prove("prepost.adb",opt=["-P", "test.gpr", "--all-vcs"])
