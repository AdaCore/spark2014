from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
contains_manual_proof = False


def replay():
    prove_all(procs=0, level=1, sparklib=True)
    prove_all(procs=0, level=4, sparklib=True)


if __name__ == "__main__":
    prove_all(replay=True, no_fail=True, sparklib=True)
