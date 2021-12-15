from test_support import prove_all

# -U should be passed in addition to --limit-subp or --limit-line for
# locations inside generics, so that all instances are analyzed.
prove_all(opt=["--limit-line=gene.adb:5", "-U"])
prove_all(opt=["--limit-line=gene2.adb:5", "-U"])
prove_all(opt=["--limit-subp=gene.ads:6", "-U"])

# The following currently does nothing, as the location of the generic
# procedure instantiation is not linked to the location of the generic
# procedure itself.
prove_all(opt=["--limit-line=gene2.adb:6", "-U"])
