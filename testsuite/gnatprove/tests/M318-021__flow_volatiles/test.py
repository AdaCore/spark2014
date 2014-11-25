from test_support import *

prove_all(opt=["-u", "caller.adb"])
prove_all(opt=["-u", "devtest.adb"])
prove_all(opt=["-u", "tests_async_readers.adb"])
prove_all(opt=["-u", "tests_async_writers.adb"])
prove_all(opt=["-u", "tests_external_state.adb"])
prove_all(opt=["-u", "types.adb"])
