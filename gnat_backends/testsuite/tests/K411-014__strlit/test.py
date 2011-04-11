from test_support import *
import glob

prove("slit.adb",opt=["-P", "test.gpr", "--all-vcs"])
