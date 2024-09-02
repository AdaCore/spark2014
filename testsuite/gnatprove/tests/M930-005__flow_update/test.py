from subprocess import call
from test_support import do_flow, gprbuild

do_flow(opt=["-u", "update_legal.adb"])
do_flow(opt=["-u", "update_uninitialized.adb"])
do_flow(opt=["-u", "update_uninitialized_2.adb"])
do_flow(opt=["-u", "update_uninitialized_3.adb"])
gprbuild(["-gnata", "main.adb"])
call(["./main"])
