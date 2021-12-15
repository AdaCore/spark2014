from test_support import prove_all

prove_all(opt=["--limit-line=test_if.ads:5:37:VC_OVERFLOW_CHECK"])
prove_all(opt=["--limit-line=test_if.adb:16:33:VC_LOOP_INVARIANT_PRESERV"])
