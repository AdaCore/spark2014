from test_support import *

do_flow(opt=["-u", "error.adb"])
do_flow(opt=["--pedantic", "-u", "pedantic.adb"])
