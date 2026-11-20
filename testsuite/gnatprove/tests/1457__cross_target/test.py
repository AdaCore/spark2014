import os

from test_support import prove_all, run_command

# Build a native driver so GNATprove can launch it on both Unix and Windows.
driver = "fake-gcc.exe" if os.name == "nt" else "fake-gcc"
process = run_command(["gcc", "fake-gcc.c", "-o", driver])
assert process.status == 0, process.out

prove_all(project="test.gpr")
