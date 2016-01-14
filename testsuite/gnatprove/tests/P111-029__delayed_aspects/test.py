from test_support import *

prove_all(opt=["-P", "test.gpr", "-u", "client1.ads"])
prove_all(opt=["-P", "test.gpr", "-u", "client2.ads"])
