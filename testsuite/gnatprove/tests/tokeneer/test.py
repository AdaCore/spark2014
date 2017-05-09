import glob
from test_support import *

def replay():
    prove_all(procs=0, opt=["--level=2", "--no-axiom-guard"], steps=None, vc_timeout=20)

prove_all(opt=["--replay", "--no-axiom-guard"], procs=4)

# testing the proof information in .spark files. See <gnatprove/spark_report>
# for the format of the .spark files
count = 0
for fn in glob.glob("gnatprove/*.spark"):
    with open(fn, "r") as f:
        d = json.load(f)
        for r in d['proof']:
            count += len(r['check_tree'])
if __name__ == "__main__":
    assert (count > 1000)

