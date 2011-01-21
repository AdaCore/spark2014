from test_support import *

gnat2why("ite.adb", "-gnat2012")
why("out.why",opt="--alt-ergo")
altergo("out_why.why")
