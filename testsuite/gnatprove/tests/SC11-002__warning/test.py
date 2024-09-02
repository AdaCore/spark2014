from test_support import prove_all, gprbuild

prove_all(sparklib=True)
gprbuild(["-P", "test.gpr", "-q", "-c", "cont.ads"])
