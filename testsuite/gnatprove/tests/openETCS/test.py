from test_support import *
from glob import glob
# Do not use Z3, as the step limit fluctuates too much between platforms, thus
# making it impossible to share a common expected output when Z3 is used.

# List of all ada units (picking .adb in most cases, except when we only
# have a spec file).
files = [f + ".adb" if os.path.isfile(f + ".adb") else f + ".ads"
         for f in set(os.path.splitext(f)[0] for f in glob("*.ad?"))]

default_level = 2
proof_level = {"step_function_test.adb" : 3}

for f in sorted(files):
    prove_all(prover=["cvc4", "altergo"],
              vc_timeout=0,
              steps=1000,
              level=proof_level.get(f, default_level),
              counterexample=False,
              opt=["-u", f])
