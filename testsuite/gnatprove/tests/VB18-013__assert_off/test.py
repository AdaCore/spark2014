from subprocess import call
from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

# Check that quantification in functional maps and sets is ok in disabled
# ghost code.

if __name__ == "__main__":
    prove_all()

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call("./main")
