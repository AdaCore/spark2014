from test_support import prove_all

prove_all()
prove_all(opt=["-f", "-u", "gen2.adb"])
