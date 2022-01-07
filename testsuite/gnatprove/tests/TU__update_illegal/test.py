from subprocess import call
from test_support import gcc

gcc("update_illegal.adb", opt=["-c", "-gnatf"])
gcc("update_illegal_2.adb", opt=["-c", "-gnatf"])
call(["gnatmake", "-gnata", "main.adb"])
call(["./main"])
