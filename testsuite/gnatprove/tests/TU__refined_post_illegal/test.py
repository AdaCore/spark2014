from subprocess import call
from test_support import *

gcc("refined_post_illegal.adb")
prove_all(opt=["-u", "refined_post_illegal_2.adb"])
call(["gnatmake", "-gnata", "main.adb"])
call(["gnatmake", "-gnata", "main2.adb"])
call(["./main"])
call(["./main2"])
