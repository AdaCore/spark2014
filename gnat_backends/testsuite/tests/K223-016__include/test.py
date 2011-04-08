from test_support import *
import glob

prove("caller.adb",opt=["-P", "test.gpr", "--all-vcs"])
