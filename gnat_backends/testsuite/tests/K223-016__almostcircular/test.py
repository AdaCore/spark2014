from test_support import *
import glob

prove("top.adb",opt=["-P", "test.gpr", "--all-vcs"])
