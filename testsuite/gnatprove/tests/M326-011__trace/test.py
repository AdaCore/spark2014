from test_support import *
import glob
import os.path

def cat_traces():
    files = glob.glob("gnatprove/*trace")
    for file in files:
        cat (file, sort=True)

prove_all(opt=["--limit-line=test.ads:4", "--proof=progressive"], steps=10)
cat_traces()
clean()
prove_all(opt=["--limit-line=test2.ads:4", "--proof=progressive"], steps=10)
cat_traces()

