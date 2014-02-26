from subprocess import call
from test_support import *

gcc("contract_cases_illegal.ads")
prove_all(opt=["-u", "contract_cases_illegal_2.adb"])

call(["gnatmake", "-gnata", "-q", "main.adb"])
call(["gnatmake", "-gnata", "-q", "main2.adb"])
call(["./main"])
call(["./main2"])

