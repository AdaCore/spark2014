from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR


def replay():
    prove_all(
        procs=0,
        level=1,
        opt=["--function-sandboxing=off"],
        check_counterexamples=False,
        sparklib=True,
    )
    prove_all(
        procs=0,
        level=4,
        vc_timeout=120,
        opt=["--function-sandboxing=off"],
        check_counterexamples=False,
        sparklib=True,
    )


if __name__ == "__main__":
    prove_all(
        replay=True,
        opt=["--function-sandboxing=off"],
        check_counterexamples=False,
        sparklib=True,
    )
