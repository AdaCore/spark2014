from subprocess import call
from test_support import prove_all

if __name__ == "__main__":
    prove_all(prover=["cvc5", "z3"])

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./test"])
