from pathlib import Path

from test_support import prove_all

prove_all()

report = Path("gnatprove/gnatprove.out").read_text()
print("==== Justified checks in gnatprove.out ====")
for line in report.splitlines():
    entry = line.strip()
    if entry.startswith(("flow_op.ads:", "proof_op.adb:")):
        print(entry)
