import glob
from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, opt=["--level=2", "--no-axiom-guard"], steps=0, vc_timeout=20, no_fail=True)

prove_all(["--no-axiom-guard"], procs=4, replay=True, no_fail=True)

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
