from test_support import prove_all, TESTDIR
from glob import glob
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

# List of all ada units (picking .adb in most cases, except when we only
# have a spec file).
files = [
    f + ".adb" if os.path.isfile(f + ".adb") else f + ".ads"
    for f in set(os.path.splitext(f)[0] for f in glob("*.ad?"))
]

for f in sorted(files):
    prove_all(
        prover=["cvc5", "z3"],
        vc_timeout=0,
        steps=3000,
        opt=["-u", f],
        sparklib=True,
    )
