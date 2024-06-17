from subprocess import check_output
import json

data = json.loads(check_output(["gnatprove", "--print-gpr-registry"]))
print(json.dumps(data, sort_keys=True, indent=4))
