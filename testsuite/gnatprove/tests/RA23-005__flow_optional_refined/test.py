from test_support import *

# Currently we have no output from --flow-show-gg, so it is safe to sort
# the ordinary check messages (and otherwise we will get random diffs).
# Once this TN is fixed and we DO GET some output from --flow-show-gg,
# then we must rethink what to do; possibly run gnatprove separately
# for p1.ads and p1-p2.ads.
do_flow(opt=["--flow-show-gg", "--no-inlining"], sort_output=True)
