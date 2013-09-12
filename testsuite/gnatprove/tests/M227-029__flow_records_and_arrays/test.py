from test_support import *
from glob import glob

do_flow(opt=sorted(glob("*.adb")))
