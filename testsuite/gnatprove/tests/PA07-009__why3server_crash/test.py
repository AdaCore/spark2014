from test_support import *

prove_all(level=1, steps=0, vc_timeout=5, opt=["-u", "binary_trees.adb", "-f", "-j0"])
