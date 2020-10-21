from test_support import *

gcc("volatiles_illegal_1.adb",opt=["-c", "-gnatf"])
gcc("volatiles_illegal_2.ads",opt=["-S", "-c", "-gnatf", "-gnatX"])
gcc("volatiles_illegal_3.ads",opt=["-S", "-c", "-gnatf"])
gcc("volatiles_illegal_4.adb",opt=["-c", "-gnatf"])
gcc("volatiles_illegal_5.adb",opt=["-c", "-gnatf"])
gcc("volatiles_illegal_6.adb",opt=["-c", "-gnatf"])
gcc("volatiles_illegal_7.adb",opt=["-c", "-gnatf"])
gcc("volatiles_illegal_8.adb",opt=["-c", "-gnatf"])
gcc("volatiles_illegal_9.adb",opt=["-c", "-gnatf"])
gcc("volatiles_illegal_10.ads",opt=["-S", "-c", "-gnatf"])
gcc("vc3.ads",opt=["-c", "-gnatf"])
