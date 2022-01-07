from test_support import prove_all

prove_all(opt=["-u", "use_float_dims.adb", "use_long_dims.adb"])
prove_all(opt=["-u", "use_dims.adb"])
