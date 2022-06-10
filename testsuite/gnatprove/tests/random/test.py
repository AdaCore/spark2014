from test_support import prove_all
from e3.os.process import Run

# Prove RTE
prove_all(steps=6000)

# Execute test program
Run(["gprbuild", "-P", "test.gpr"])
process = Run(["./main"])
print(process.out)
