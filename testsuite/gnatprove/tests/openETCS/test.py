from test_support import prove_all
from glob import glob
import os.path

# List of all ada units (picking .adb in most cases, except when we only
# have a spec file).
files = [
    f + ".adb" if os.path.isfile(f + ".adb") else f + ".ads"
    for f in set(os.path.splitext(f)[0] for f in glob("*.ad?"))
]

for f in sorted(files):
    prove_all(
        prover=["cvc4", "z3"],
        vc_timeout=0,
        steps=3000,
        counterexample=False,
        opt=["-u", f],
    )
