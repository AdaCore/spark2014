from test_support import gcc, prove_all

gcc("global_illegal.ads", opt=["-c", "-gnatf"])
gcc("global_illegal_2.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "global_illegal_3.adb", "-cargs", "-gnatf"])
