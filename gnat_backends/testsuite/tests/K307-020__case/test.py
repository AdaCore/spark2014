from test_support import *
import glob

prove("casing.adb",opt=["-P", "test.gpr", "--all-vcs"])
