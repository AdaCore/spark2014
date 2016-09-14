from test_support import *

do_flow(opt=["-u", "init.adb"])
do_flow(opt=["-u", "init_2.ads"])
do_flow(opt=["-u", "initializes_legal.adb"])
do_flow(opt=["-u", "initializes_illegal.adb"])
do_flow(opt=["-u", "initializes_illegal_2.adb"])
do_flow(opt=["-u", "initializes_illegal_3.ads"])
