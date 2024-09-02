from subprocess import call
from test_support import gcc, prove_all, gprbuild

gcc("loop_related_illegal.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "loop_related_illegal_2.adb", "-cargs", "-gnatf"])
prove_all(opt=["-u", "loop_related_illegal_3.adb", "-cargs", "-gnatf"])
gprbuild(["-gnata", "-q", "main.adb"])
gprbuild(["-gnata", "-q", "main2.adb"])
call(["./main"])
call(["./main2"])
