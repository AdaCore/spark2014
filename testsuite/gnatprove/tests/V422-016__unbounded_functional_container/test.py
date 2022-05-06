from subprocess import call
from test_support import prove_all

if __name__ == "__main__":
    prove_all(steps=1282)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./infinite_sequence"])

