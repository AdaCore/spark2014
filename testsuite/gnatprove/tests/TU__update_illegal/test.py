from subprocess import call
from test_support import gcc, gprbuild

gcc("update_illegal.adb", opt=["-c", "-gnatf"])
gcc("update_illegal_2.adb", opt=["-c", "-gnatf"])
gprbuild(["-gnata", "main.adb"])
call(["./main"])
