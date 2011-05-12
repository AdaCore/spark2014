from test_support import *
import glob

prove("divide.adb",opt=["-P", "test.gpr", "--all-vcs"])
