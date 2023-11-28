from subprocess import call
from test_support import prove_all, create_sparklib
import os

os.environ["SPARKLIB_BODY_MODE"] = "On"

# Check that aggregates of functional containers work as expected.

if __name__ == "__main__":
    prove_all(sparklib=True)

    create_sparklib()
    call(["gprbuild", "-q", "-P", "test.gpr"])
    call("./main")
