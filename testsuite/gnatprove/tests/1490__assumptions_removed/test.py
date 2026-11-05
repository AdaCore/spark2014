import json
from pathlib import Path

from test_support import prove_all, run_command

print("===== deprecated switch on command line =====")
prove_all(opt=["--assumptions"], exit_status=0)
spark_file = Path("gnatprove/main.spark")
data = json.loads(spark_file.read_text())
assert "assumptions" not in data
assert data["pragma_assume"]

report = Path("gnatprove/gnatprove.out")
original_report = report.read_text()
assert "pragma Assume statements:" in original_report

print("===== deprecated switch in project file =====")
prove_all(project="legacy.gpr", opt=["--output-msg-only"], exit_status=0)
assert report.read_text() == original_report

# Older artifacts may still contain dependency rules. Report generation must
# ignore these while preserving the ordinary results and pragma Assume list.
entity = data["pragma_assume"][0]["entity"]
token = {"predicate": "CLAIM_AORTE", "arg": entity}
data["assumptions"] = [{"claim": token, "assumptions": [token]}]
spark_file.write_text(json.dumps(data))
process = run_command(
    ["gnatprove", "-P", "test.gpr", "--output-msg-only", "--report=provers"]
)
assert process.status == 0, process.out
assert report.read_text() == original_report
print("Legacy assumption dependencies ignored; ordinary report preserved")
