from test_support import *

prove("simple_unc_array.adb",opt=["-P", "test.gpr", "--all-vcs"])
