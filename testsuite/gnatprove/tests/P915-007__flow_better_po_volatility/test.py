from test_support import clean, do_flow
from glob import glob

for i, fn in enumerate(sorted(glob("*.adb"))):
    if i > 0:
        print
    print("=== %s ===" % fn)
    clean()
    do_flow(opt=["-u", fn])
