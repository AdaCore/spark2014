from test_support import *
import os.path
import glob

prove("strlit.adb",opt=["-P", "test.gpr", "--all-vcs"])
cat(os.path.join ("gnatprove", "strlit.alfa"))
