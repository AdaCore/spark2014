from test_support import *

# "purity" specs are violated by these bodies
do_flow(opt=["-u", "impure_package.adb"])
do_flow(opt=["-u", "impure_procedure.adb"])

# but here the purity should be assumed
do_flow(opt=["-u", "call.adb"])
