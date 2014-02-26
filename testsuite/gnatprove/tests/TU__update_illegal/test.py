from subprocess import call
from test_support import *

gcc("update_illegal.adb")
gcc("update_illegal_2.adb")
call(["gnatmake", "-gnata", "main.adb"])
call(["./main"])
