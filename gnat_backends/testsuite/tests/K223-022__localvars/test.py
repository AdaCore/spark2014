from test_support import *
import glob

prove("loc.adb",opt=["-P", "test.gpr", "--all-vcs"])
