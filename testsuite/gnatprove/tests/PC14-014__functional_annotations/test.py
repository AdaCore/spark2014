from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, opt=["--no-axiom-guard", "--counterexamples=off"], level=4)

if __name__ == "__main__":
    prove_all(opt=["--no-axiom-guard",
                   "--counterexamples=off"],
              replay=True)
