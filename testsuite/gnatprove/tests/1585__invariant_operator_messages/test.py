from test_support import (
    prove_all,
    capture_prove_all,
    find_sarif_results,
    sarif_result_property,
)

prove_all()

results = find_sarif_results(rule_id="VC_RAISE")
reasons = [
    sarif_result_property(result, "reasonForCheck", parent="gnatprove")
    for result in results
]
assert '"&" allows propagating no exceptions' in reasons, reasons
print("SARIF reason preserves the unescaped operator name")

output = capture_prove_all(opt=["-u", "unexpected.adb", "--output=pretty"])
assert 'reason for check: "&" allows propagating no exceptions' in output, output
print("Pretty output preserves the operator name")
