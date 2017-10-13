from subprocess import call
from test_support import *

do_flow()
call(["gnatmake", "-q", "main.adb"])
