from test_support import *
from glob import *

body_files = set(glob("*.adb"))

files = []
for spec in sorted(glob("*.ads")):
    body = spec.replace(".ads", ".adb")
    if body in body_files:
        files.append(body)
    else:
        files.append(spec)

for i, fn in enumerate(files):
    if i > 0:
        print()
    print("=== %s ===" % fn)
    do_flow(opt=["-u", fn])
