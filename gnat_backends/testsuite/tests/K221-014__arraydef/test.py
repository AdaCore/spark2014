from test_support import *
import glob

prove("arraydef.adb",opt=["-P", "test.gpr", "--all-vcs"])
