from test_support import *
# run GNATprove separately on failing input foo.adb ...
do_flow(opt=["-u", "foo.adb"])
# ... and correct code in other units.
do_flow(opt=["-u", "main1.adb", "main2.adb", "main3.adb", "main4.adb"])
