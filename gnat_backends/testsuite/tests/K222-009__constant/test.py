from test_support import *
import glob

prove("const.adb",opt=["-P", "test.gpr", "--all-vcs"])
