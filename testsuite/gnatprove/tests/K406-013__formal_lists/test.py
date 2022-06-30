from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

def replay():
    prove_all(prover=["cvc5", "z3"], procs=0, level=4, counterexample=False, sparklib=True)


if __name__ == "__main__":
    prove_all(prover=["cvc5", "z3"], replay=True, counterexample=False, sparklib=True)
