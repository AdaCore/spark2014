from test_support import prove_all

prove_all(project="test1.gpr", opt=["-u", "t.adb"])
prove_all(project="test2.gpr", opt=["-u", "t.adb"])
prove_all(project="test3.gpr", opt=["-u", "t.adb"])
prove_all(opt=["-u", "po_t.adb"])
prove_all(opt=["-u", "po_t2.adb"])
prove_all(opt=["-u", "po_t3.adb"])
prove_all(opt=["-u", "po_t4.adb"])
prove_all(opt=["-u", "po_t5.adb"])
prove_all(opt=["-u", "main.adb"])
prove_all(opt=["-u", "po_t7.adb"])
prove_all(opt=["-u", "use_po_t8.adb"])
