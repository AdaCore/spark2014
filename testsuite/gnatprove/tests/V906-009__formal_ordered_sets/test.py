from e3.os.process import Run
from test_support import prove_all, gprbuild, print_sorted
import os

contains_manual_proof = False
os.environ["SPARKLIB_BODY_MODE"] = "On"


def replay():
    prove_all(level=4, procs=0, sparklib=True)


if __name__ == "__main__":
    prove_all(replay=True, sparklib=True)

    gprbuild(["-q", "-P", "test.gpr"])
    process = Run(["./obj/test"])
    print_sorted(str.splitlines(process.out))
