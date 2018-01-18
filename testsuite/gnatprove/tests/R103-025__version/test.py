from test_support import *
from gnatpython.ex import Run

# test the version output of gnatprove. We remove:
# - the gnatprove version, which changes too much
# - the prover locations
# We keep prover output, because it changes only rarely.

p = Run(["gnatprove", "--version"])
l = p.out.splitlines()
# drop first line of output
l = l[1:]
for line in l:
    # remove everything before the dash
    # there might be no dash, but the code still works
    elts = line.split(':')
    print elts[-1]
