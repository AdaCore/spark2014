from test_support import *
from e3.os.process import Run

# test should only be run when aunit is present

proc = Run(["gnat", "ls", "-Paunit"])
output = str.splitlines(proc.out)
output = grep(".*project file .* not found.*",output)
if output == []:
    prove_all()
