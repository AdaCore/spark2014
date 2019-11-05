from test_support import *

do_flow(opt=["-u", "bad_spec.ads"])
do_flow(opt=["-u", "bad_spec_prag.ads"])
do_flow(opt=["-u", "bad.adb"])
prove_all(opt=["-u", "pack.adb"])
