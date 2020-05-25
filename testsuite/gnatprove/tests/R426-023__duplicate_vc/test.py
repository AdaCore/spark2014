from test_support import *
from e3.env import Env
import time
import json

# This test is for a bug of gnatwhy3 which, in debug mode, would reuse the
# same files for different checks with the exact same location *and* reason
# (when run in parallel).
# This eventually lead to inconsistency issue when one of the check is proved
# and not the other. The file main_range.mlw reproduce this behavior by defining
# two checks with reason VC_RANGE_CHECK: one being provable and not the other.

RESULTS="results"
RESULT="result"
ID="id"

installdir = spark_install_path()
bindir = os.path.join(installdir, 'libexec', 'spark', 'bin')
Env().add_path(bindir)

cmd = ["gnatwhy3",
       "--timeout", "1",
       "--steps", "0",
       "--prover", "cvc4",
       "--proof", "per_check",
       "--debug",
       "--force",
       "-j", "2",
       "--counterexample", "off",
       "main_range.mlw"]

result = Run (cmd, timeout=30)

result_out = result.out
j = json.loads(result_out)
results = j[RESULTS]

print ("Result per id are the following in debug mode:")

for result in results:
    print(str(result[ID]) + ":" + str(result[RESULT]))


cmd = ["gnatwhy3",
       "--timeout", "1",
       "--steps", "0",
       "--prover", "cvc4",
       "--proof", "per_check",
       "--standalone",
       "--force",
       "-j", "2",
       "--counterexample", "off",
       "main_range.mlw"]

result = Run (cmd, timeout=30)

result_out = result.out
j = json.loads(result_out)
results = j[RESULTS]

print ("Result per id are the following in normal mode:")

for result in results:
    print(str(result[ID]) + ":" + str(result[RESULT]))
