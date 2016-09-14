from subprocess import call
from test_support import *

do_flow(opt=["-u", "update_legal.adb"])
do_flow(opt=["-u", "update_uninitialized.adb"])
do_flow(opt=["-u", "update_uninitialized_2.adb"])
do_flow(opt=["-u", "update_uninitialized_3.adb"])
call(["gnatmake", "-gnata", "main.adb"])
call(["./main"])
