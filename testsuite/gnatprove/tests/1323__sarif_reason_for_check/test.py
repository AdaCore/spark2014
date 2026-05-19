import contextlib
import io
import json
import os.path

from test_support import prove_all

EXPECTED = "result of addition must fit in a 32-bits machine integer"


stream = io.StringIO()
with contextlib.redirect_stdout(stream):
    prove_all()

output = stream.getvalue()

if "[reason for check: " + EXPECTED + "]" not in output:
    print("Missing in CLI:", EXPECTED)
else:
    print("CLI reason present")

with open(os.path.join("gnatprove", "gnatprove.sarif")) as f:
    sarif = json.load(f)

for result in sarif["runs"][0].get("results", []):
    props = result.get("properties", {})
    if (
        result.get("ruleId") == "VC_OVERFLOW_CHECK"
        and props.get("gnatprove/reasonForCheck") == EXPECTED
    ):
        print("SARIF reason:", props["gnatprove/reasonForCheck"])
        break
else:
    print("Missing in SARIF:", EXPECTED)
