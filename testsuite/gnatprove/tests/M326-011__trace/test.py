from test_support import *
import glob
import os.path

prove_all(opt=["--limit-line=test.ads:4", "--proof=then_split"], steps=10)
cat (os.path.join("gnatprove","test.ads_4_18_postcondition.trace"), sort=True)
prove_all(opt=["--limit-line=test2.ads:4", "--proof=then_split"], steps=10)
cat (os.path.join("gnatprove","test2.ads_4_18_postcondition.trace"), sort=True)

