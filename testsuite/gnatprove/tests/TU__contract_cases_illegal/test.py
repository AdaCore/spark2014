from subprocess import call
from test_support import gcc, prove_all

gcc("contract_cases_illegal.ads", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "contract_cases_illegal_2.adb", "-cargs", "-gnatf"])

call(["gnatmake", "-gnata", "-q", "main.adb"])
call(["gnatmake", "-gnata", "-q", "main2.adb"])
call(["./main"])
call(["./main2"])
