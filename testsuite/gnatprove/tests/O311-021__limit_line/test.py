from test_support import prove_all

prove_all(opt=["--limit-subp=oper.ads:3", "--limit-line=oper-float_sub.adb:4"])
prove_all(opt=["--limit-subp=oper.adb:4", "--limit-line=oper-float_sub_2.adb:4"])
