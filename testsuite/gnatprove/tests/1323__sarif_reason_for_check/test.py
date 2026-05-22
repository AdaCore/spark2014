from test_support import (
    capture_prove_all,
    find_sarif_results,
    sarif_result_property,
)

EXPECTED = "result of addition must fit in a 32-bits machine integer"
PROPERTY = "gnatprove/reasonForCheck"

output = capture_prove_all()

if "[reason for check: " + EXPECTED + "]" not in output:
    print("Missing CLI reasonForCheck:", EXPECTED)
else:
    print("CLI reasonForCheck:", EXPECTED)

for result in find_sarif_results(
    rule_id="VC_OVERFLOW_CHECK",
    predicate=lambda item: sarif_result_property(item, PROPERTY) == EXPECTED,
):
    print("SARIF reasonForCheck:", sarif_result_property(result, PROPERTY))
    break
else:
    print("Missing SARIF reasonForCheck:", EXPECTED)
