from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

if __name__ == "__main__":
    prove_all(
        check_counterexamples=False, steps=1400, sparklib=True, opt=["--no-axiom-guard"]
    )
