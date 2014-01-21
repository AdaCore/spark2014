from test_support import *
from gnatpython.ex import Run

# test should only be run when aunit is present

proc = Run(["gnatls", "-Paunit"])
output = str.splitlines(proc.out)
output = grep(".*project file .* not found.*",output)
if output == []:
    prove_all()
