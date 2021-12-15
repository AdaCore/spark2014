from test_support import prove_all

prove_all(opt=["-P", "test.gpr", "-u", "client0.ads"])
prove_all(opt=["-P", "test.gpr", "-u", "client1.ads"])
prove_all(opt=["-P", "test.gpr", "-u", "client2.ads"])
prove_all(opt=["-P", "test.gpr", "-u", "client3.ads"])
