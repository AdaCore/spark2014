from subprocess import call
from test_support import prove_all, gprbuild

# Check that quantification in functional maps and sets is ok in disabled
# ghost code.

if __name__ == "__main__":
    prove_all(sparklib=True)

    gprbuild(["-q", "-P", "test.gpr"])
    call("./main")
