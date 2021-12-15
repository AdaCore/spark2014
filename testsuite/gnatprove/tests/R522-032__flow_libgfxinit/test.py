from test_support import do_flow

# ??? after closing the TN the --mode=flow should be removed while
# test should be qualified as "large"; this switch is a temporary
# solution to make hacking on the flow analysis easier. The flow
# analysis alone takes ~15s on my machine, while proof takes ~1m30s.

do_flow(opt=["--no-loop-unrolling", "--no-inlining", "--mode=flow"])
