from glob import glob
import json
from test_support import flow_gg

flow_gg()

print("Generated global .gg contents:")
for filename in sorted(glob("gnatprove/*.gg")):
    print("filename:", filename)
    file = open(filename)
    data = json.load(file)
    file.close()
    print("contents:")
    print(json.dumps(data, sort_keys=True, indent=2))
