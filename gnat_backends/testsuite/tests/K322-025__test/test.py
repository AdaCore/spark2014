from test_support import *
import glob

prove("test.adb",opt=["-P", "test.gpr", "--all-vcs"])
