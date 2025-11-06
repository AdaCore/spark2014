from subprocess import call
from test_support import prove_all, gprbuild

contains_manual_proof = False


def replay():
    prove_all(level=4, procs=0, sparklib=True, sparklib_bodymode=True)


if __name__ == "__main__":
    prove_all(replay=True, sparklib=True, sparklib_bodymode=True)

    gprbuild(["-q", "-P", "test.gpr"])
    call(["./obj/test"])
