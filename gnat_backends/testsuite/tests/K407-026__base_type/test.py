from test_support import *

prove("base_type.adb",opt=["-P", "test.gpr", "--all-vcs"])

