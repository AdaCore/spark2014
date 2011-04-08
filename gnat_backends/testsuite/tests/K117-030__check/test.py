from test_support import *
import glob

prove("check.adb",opt=["-P", "test.gpr", "--all-vcs"])
