from test_support import *
import glob

prove("add.adb",opt=["-P", "test.gpr", "--all-vcs"])
