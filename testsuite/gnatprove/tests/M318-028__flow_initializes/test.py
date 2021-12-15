from test_support import do_flow
from glob import glob

do_flow(opt=sorted(glob("*.adb")))
