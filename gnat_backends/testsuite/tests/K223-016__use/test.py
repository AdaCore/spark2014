from test_support import *
import glob

prove("user.adb",opt=["-P", "test.gpr", "--all-vcs"])
