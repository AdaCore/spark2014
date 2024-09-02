from subprocess import call
from test_support import gcc, prove_all, gprbuild

gcc("refined_post_illegal.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "refined_post_illegal_2.adb", "-cargs", "-gnatf"])
gprbuild(["-gnata", "main.adb"])
gprbuild(["-gnata", "main2.adb"])
call(["./main"])
call(["./main2"])
