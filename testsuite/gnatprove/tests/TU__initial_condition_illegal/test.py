from test_support import *

gcc("initial_condition_illegal.adb",opt=["-c", "-gnatf"])
prove_all(opt=["-u", "initial_condition_illegal_2.adb", "-cargs", "-gnatf"])
prove_all(opt=["-u", "initial_condition_illegal_3.adb", "-cargs", "-gnatf"])
prove_all(opt=["-u", "initial_condition_illegal_4.adb", "-cargs", "-gnatf"])
