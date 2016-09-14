from test_support import *

do_flow(opt=["-u", "caller.adb"])
do_flow(opt=["-u", "devtest.adb"])
do_flow(opt=["-u", "tests_async_readers.adb"])
do_flow(opt=["-u", "tests_async_writers.adb"])
do_flow(opt=["-u", "tests_external_state.adb"])
do_flow(opt=["-u", "types.adb"])
