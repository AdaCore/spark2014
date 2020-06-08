#!/bin/sh

# This script is useful to bisect the spark2014 repo under the following assumptions:
# - An identified test fails with DIFF output on HEAD and doesn't fail n
#   commits earlier
# - most commits compile (e.g. there are no commits that depend on changes in
#   gnat repo)

# Do not run the script directly. To use the script, do the following:
# 1. go to the toplevel of the spark2014 repo, make sure you have no local changes.
# 2. Start the bisect for e.g. the 20 last commits:
#    $ git bisect start HEAD HEAD~20
# 3. Run automatic bisect via git
#    $ git bisect run scripts/bisect.sh <testname>
# 4. clean up afterwards
#    $ git bisect reset

make || exit 125
make install-all || exit 125
cd testsuite/gnatprove
! ./run-tests $1 --exact 2>&1 | grep DIFF
