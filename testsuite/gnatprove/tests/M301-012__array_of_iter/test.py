from test_support import prove_all

prove_all(opt=["-u", "iter_array.adb"])
# iterator on multi dimensional array is not yet supported
prove_all(opt=["-u", "iter_multi_array.adb"])
