from test_support import *
# run GNATprove separately on failing input foo.adb ...
prove_all(opt=["-u", "foo.adb"])
# ... and correct code in other units.
prove_all(opt=["-u", "main1.adb", "main2.adb", "main3.adb", "main4.adb"])
