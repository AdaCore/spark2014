from test_support import *
import glob

prove("prepost.adb",opt=["-P", "test.gpr", "--all-vcs"])
