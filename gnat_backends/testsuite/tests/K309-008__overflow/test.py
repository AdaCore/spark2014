from test_support import *
import glob

prove("over.adb",opt=["-P", "test.gpr", "--all-vcs"])
