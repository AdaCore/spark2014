from test_support import *

# This test is run with mode flow. It is intended to demonstrate possible
# messages and warnings issued by flow analysis. In particular, it demonstrates
# undischarged aliasing checks which cause GNATprove to fail on prove mode
# see O429-003

prove_all(opt=["--mode=flow"])
