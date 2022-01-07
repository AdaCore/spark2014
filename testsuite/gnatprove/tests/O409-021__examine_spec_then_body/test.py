from test_support import clean, prove_all

clean()
prove_all(opt=["-u", "test.ads"])
prove_all(opt=["-u", "test.adb"])
