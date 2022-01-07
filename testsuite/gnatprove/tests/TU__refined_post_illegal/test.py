from subprocess import call
from test_support import gcc, prove_all

gcc("refined_post_illegal.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "refined_post_illegal_2.adb", "-cargs", "-gnatf"])
call(["gnatmake", "-gnata", "main.adb"])
call(["gnatmake", "-gnata", "main2.adb"])
call(["./main"])
call(["./main2"])
