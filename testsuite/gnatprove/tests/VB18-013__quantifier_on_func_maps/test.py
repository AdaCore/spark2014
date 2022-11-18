from subprocess import run
from test_support import TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

# Check that quantification in functional maps cannot be executed

if __name__ == "__main__":
    process = run(["gprbuild", "-q", "-P", "test.gpr"], capture_output=True)
    if process.returncode == 0:
        print("Should have failed at link time")
