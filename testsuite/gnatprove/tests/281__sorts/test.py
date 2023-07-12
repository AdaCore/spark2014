from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR


def replay():
    prove_all(level=2, opt=["--function-sandboxing=off"], sparklib=True, procs=0)


if __name__ == "__main__":
    prove_all(
        replay=True, opt=["--function-sandboxing=off"], sparklib=True, no_fail=True
    )
