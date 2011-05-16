from test_support import *
import glob

prove("b.adb",opt=["-P", "test.gpr", "--all-vcs"])
