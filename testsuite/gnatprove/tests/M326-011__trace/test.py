from test_support import *
import glob
import os.path

def cat_traces():
    files = glob.glob("gnatprove/*postcondition*trace")
    for file in files:
        cat (file, sort=True)

prove_all(opt=["--limit-line=test.ads:4", "--proof=progressive"], cache_allowed=False)
cat_traces()
clean()
prove_all(opt=["--limit-line=test2.ads:4", "--proof=progressive"], cache_allowed=False)
cat_traces()
