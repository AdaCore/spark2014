from test_support import *
import glob

prove("constr.adb",opt=["-P", "test.gpr", "--all-vcs"])
