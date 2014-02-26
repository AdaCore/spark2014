from subprocess import call
from test_support import *

prove_all(opt=["-u", "update_legal.adb"])
prove_all(opt=["-u", "update_uninitialized.adb"])
prove_all(opt=["-u", "update_uninitialized_2.adb"])
prove_all(opt=["-u", "update_uninitialized_3.adb"])
call(["gnatmake", "-gnata", "main.adb"])
call(["./main"])

