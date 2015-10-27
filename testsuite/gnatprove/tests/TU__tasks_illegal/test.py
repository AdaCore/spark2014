from test_support import *

prove_all(opt=["-P", "test1.gpr", "-u", "t.adb"])
prove_all(opt=["-P", "test2.gpr", "-u", "t.adb"])
prove_all(opt=["-P", "test3.gpr", "-u", "t.adb"])
prove_all(opt=["-P", "test.gpr", "-u", "po_t.adb"])
prove_all(opt=["-P", "test.gpr", "-u", "po_t2.adb"])
prove_all(opt=["-P", "test.gpr", "-u", "po_t3.adb"])
prove_all(opt=["-P", "test.gpr", "-u", "po_t4.adb"])
prove_all(opt=["-P", "test.gpr", "-u", "po_t5.adb"])
