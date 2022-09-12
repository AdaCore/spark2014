from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

def replay():
    prove_all(procs=0, opt=["--no-axiom-guard", "--counterexamples=off"], level=4, sparklib=True)


if __name__ == "__main__":
    prove_all(opt=["--no-axiom-guard", "--counterexamples=off"], replay=True, sparklib=True)
