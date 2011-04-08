from test_support import *
import glob

prove("anon.adb",opt=["-P", "test.gpr", "--all-vcs"])
