from test_support import gcc, prove_all

gcc("depends_illegal.ads", opt=["-c", "-gnatf"])
gcc("depends_illegal_2.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "depends_illegal_3.adb", "-cargs", "-gnatf"])
prove_all(opt=["-u", "depends_illegal_4.adb", "-cargs", "-gnatf"])
