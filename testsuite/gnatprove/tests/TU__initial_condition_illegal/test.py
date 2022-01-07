from test_support import prove_all

prove_all(opt=["-u", "initial_condition_illegal_2.adb", "-cargs", "-gnatf"])
prove_all(opt=["-u", "initial_condition_illegal_3.adb", "-cargs", "-gnatf"])
prove_all(opt=["-u", "initial_condition_illegal_4.adb", "-cargs", "-gnatf"])
