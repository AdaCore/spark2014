from test_support import *
from glob import glob

do_flow(opt=["--flow-show-gg", "--no-inlining", "-u"] + sorted(glob("*.ads")), sort_output=False)
