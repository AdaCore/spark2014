from subprocess import call
from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARK_LIBRARIES_OBJECT_DIR"] = TESTDIR

if __name__ == "__main__":
    prove_all()

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./obj/test"])
