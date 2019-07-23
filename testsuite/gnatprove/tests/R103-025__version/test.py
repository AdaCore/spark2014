from test_support import *
from gnatpython.ex import Run

# test the version output of gnatprove.
# Typical output is like this:
#   $ gnatprove --version
#   <gnatprove version>
#   <full-path-to-prover> : <version output for prover>
# Z3 output looks like this:
#   Z3 version <bla> - 64 bit
# We remove:
# - the gnatprove version, which changes too much
# - the prover locations
# - platform (32bits/64bits) in Z3 output

# We remove LD_LIBRARY_PATH which is set by the GNAT compiler dependency.
# In this way we can test if the provers work without this env var.
# ??? os.unsetenv didn't work, so setting to empty string instead

os.environ['LD_LIBRARY_PATH'] = ''

p = Run(["gnatprove", "--version"])
l = p.out.splitlines()
# drop first line of output
l = l[1:]
for line in l:
    # remove everything before the colon, to remove path info
    # there might be no colon, but the code still works
    elts = line.split(':')
    text = elts[-1]

    # remove everything after " - ", to remove mention of platform in z3
    # output
    elts = text.split(" - ")
    text = elts[0]
    print text
