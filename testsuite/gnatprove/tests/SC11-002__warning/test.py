from test_support import gcc, prove_all

gcc("cont.ads", opt=["-c"])
prove_all()
