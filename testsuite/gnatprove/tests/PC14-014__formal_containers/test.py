from subprocess import call
from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR


def replay():
    prove_all(
        procs=0,
        opt=["--function-sandboxing=off", "--counterexamples=off"],
        level=2,
        sparklib=True,
    )
    prove_all(
        procs=0,
        opt=["--function-sandboxing=off", "--counterexamples=off"],
        level=4,
        sparklib=True,
    )


if __name__ == "__main__":
    prove_all(
        opt=["--function-sandboxing=off", "--counterexamples=off"],
        replay=True,
        sparklib=True,
    )

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./run_tests"])
