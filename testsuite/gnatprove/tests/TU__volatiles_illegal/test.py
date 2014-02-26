from test_support import *

gcc("volatiles_illegal_1.adb")
gcc("volatiles_illegal_2.ads", "-S")
gcc("volatiles_illegal_3.ads", "-S")
gcc("volatiles_illegal_4.adb")
gcc("volatiles_illegal_5.adb")
gcc("volatiles_illegal_6.adb")
gcc("volatiles_illegal_7.adb")
gcc("volatiles_illegal_8.adb")
gcc("volatiles_illegal_9.adb")
gcc("volatiles_illegal_10.ads", "-S")
