from test_support import prove_all

prove_all(opt=["-u", "types_and_subtypes_illegal.ads", "-cargs", "-gnatf"])
prove_all(opt=["-u", "types_and_subtypes_illegal_2.adb", "-cargs", "-gnatf"])
