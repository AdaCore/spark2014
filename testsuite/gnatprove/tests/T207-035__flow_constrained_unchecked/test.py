from test_support import *

# Proof checks are intentionally disabled, because they distract from the
# inconsistent flow messages, which are the main point of this test.

print("INLINING ENABLED:")
do_flow(opt=["--mode=flow"])
print

print("INLINING DISABLED:")
do_flow(opt=["--mode=flow", "--no-inlining"])
