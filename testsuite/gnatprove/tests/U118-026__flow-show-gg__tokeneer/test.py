from glob import glob
from test_support import cat, flow_gg

flow_gg()

print("Generated global .gg contents:")
for file in sorted(glob("gnatprove/*.gg")):
    print("filename:", file)
    print("contents:")
    cat(file)
