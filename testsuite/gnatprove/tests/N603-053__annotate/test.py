from test_support import prove_all

prove_all(opt=["-u", "warn_not_suppr.adb"])
prove_all(opt=["-u", "syntax.adb"])
prove_all(opt=["-u", "suppr.adb"])
