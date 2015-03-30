from test_support import *

prove_all(opt=["-u", "types_and_subtypes_illegal.adb"])
gcc("types_and_subtypes_illegal_2.adb")
