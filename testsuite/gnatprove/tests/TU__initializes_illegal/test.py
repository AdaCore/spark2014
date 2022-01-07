from test_support import gcc, prove_all

gcc("initializes_illegal.adb", opt=["-c", "-gnatf"])
gcc("initializes_illegal_3.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "initializes_illegal_4.adb", "-cargs", "-gnatf"])
gcc("initializes_illegal_5.adb", opt=["-c", "-gnatf"])
prove_all(opt=["-u", "initializes_illegal_6.adb", "-cargs", "-gnatf"])
