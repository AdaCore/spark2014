from test_support import *
do_flow(opt=["-P", "test.gpr", "-u", "legal"])
do_flow(opt=["-P", "test.gpr", "-u", "illegal"])
