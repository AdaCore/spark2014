from test_support import *
from glob import glob
import os

do_flow(opt=["--flow-show-gg", "--no-inlining"] + sorted(glob("*.ads")), sort_output=False)

print("Generated global .gg contents:")
for file in sorted(glob("gnatprove/*.gg")):
    print("filename:", file)
    print("contents:")
    cat(file)
