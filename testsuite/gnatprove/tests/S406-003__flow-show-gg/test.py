from test_support import do_flow
from glob import glob
import json

do_flow(
    opt=["--flow-show-gg", "--no-inlining"] + sorted(glob("*.ad[sb]")),
    sort_output=False,
)

print("Generated global .gg contents:")
for filename in sorted(glob("gnatprove/*.gg")):
    print("filename:", filename)
    file = open(filename)
    data = json.load(file)
    file.close()
    print("contents:")
    print(json.dumps(data, sort_keys=True, indent=4))
