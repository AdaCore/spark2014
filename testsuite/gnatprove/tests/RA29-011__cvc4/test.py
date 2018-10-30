from test_support import Run

process = Run(["cvc4", "--show-config"])
lines = process.out.splitlines()
# first three lines of cvc4 output contain date and exact compiler version, so
# remove this output. We also remove the "scm" line which refers to the exact
# git commit in some builds.
for line in lines[3:]:
    if not line.startswith("scm"):
        print line
