from test_support import *

# Analysis of both units is expected to fail in phase 1, so we need to
# explicitly analyze them.
do_flow(opt=["-u", "proof_in_ghost.adb"])
do_flow(opt=["-u", "proof_in_ghost_with_depends.adb"])
