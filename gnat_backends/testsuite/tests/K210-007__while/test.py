from test_support import *
import glob

prove("s.adb",opt=["-P", "test.gpr", "--all-vcs"])
