from test_support import *

prove("tab_init.adb",opt=["-P", "test.gpr", "--all-vcs"])
