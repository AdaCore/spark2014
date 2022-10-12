from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
contains_manual_proof = False


def replay():
    prove_all(
        procs=0,
        steps=0,
        vc_timeout=20,
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
