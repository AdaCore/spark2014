from subprocess import call
from test_support import *

gcc("loop_related_illegal.adb")
prove_all(opt=["-u", "loop_related_illegal_2.adb"])
prove_all(opt=["-u", "loop_related_illegal_3.adb"])
call(["gnatmake", "-gnata", "-q", "main.adb"])
call(["gnatmake", "-gnata", "-q", "main2.adb"])
call(["./main"])
call(["./main2"])

