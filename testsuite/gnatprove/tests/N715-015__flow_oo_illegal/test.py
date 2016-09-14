from test_support import *

do_flow(opt=["-u", "illegal_1.adb"])
do_flow(opt=["-u", "root.adb"])
do_flow(opt=["-u", "simple_illegal_with_contracts.adb"])
do_flow(opt=["-u", "simple_illegal_without_contracts.adb"])
