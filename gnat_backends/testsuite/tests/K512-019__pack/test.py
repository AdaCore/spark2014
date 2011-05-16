from test_support import *
import glob

prove("pack.adb",opt=["-P", "test.gpr", "--all-vcs"])
