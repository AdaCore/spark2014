import glob
from test_support import *
prove_all(opt=["--replay"], procs=4)

# testing the proof information in .spark files. See <gnatprove/spark_report>
# for the format of the .spark files
count = 0
for fn in glob.glob("gnatprove/*.spark"):
    with open(fn, "r") as f:
        d = json.load(f)
        for r in d['proof']:
            count += len(r['check_tree'])
assert (count > 1000)

