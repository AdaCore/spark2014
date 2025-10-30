from subprocess import call
from test_support import prove_all, create_sparklib, gprbuild

# Check that aggregates of functional containers work as expected.

if __name__ == "__main__":
    prove_all(sparklib=True)

    create_sparklib()
    gprbuild(["-q", "-P", "test.gpr"])
    call("./main")
