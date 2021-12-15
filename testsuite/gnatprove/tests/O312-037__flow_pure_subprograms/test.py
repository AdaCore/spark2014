from test_support import do_flow

# "purity" specs are violated by these bodies
do_flow(opt=["-u", "impure_package.adb"])

# but here the purity should be assumed
do_flow(opt=["-u", "call.adb"])
