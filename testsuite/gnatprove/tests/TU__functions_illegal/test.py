from test_support import gcc, prove_all

gcc("functions_illegal.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "functions_illegal_2.adb", "-cargs", "-gnatf"])
