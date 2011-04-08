from test_support import *
import glob

prove("localcst.adb",opt=["-P", "test.gpr", "--all-vcs"])
