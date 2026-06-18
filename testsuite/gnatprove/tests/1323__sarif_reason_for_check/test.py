from test_support import (
    capture_prove_all,
    find_sarif_results,
    sarif_result_property,
)

EXPECTED = "result of addition must fit in a 32-bits machine integer"
PARENT_PROPERTY = "gnatprove"
CHILD_PROPERTY = "reasonForCheck"

output = capture_prove_all()

if "[reason for check: " + EXPECTED + "]" not in output:
    print(f"Missing CLI {CHILD_PROPERTY}:", EXPECTED)
else:
    print(f"CLI {CHILD_PROPERTY}:", EXPECTED)

for result in find_sarif_results(
    rule_id="VC_OVERFLOW_CHECK",
    predicate=lambda item: sarif_result_property(
        item, CHILD_PROPERTY, parent=PARENT_PROPERTY
    )
    == EXPECTED,
):
    print(
        f"SARIF {CHILD_PROPERTY}:",
        sarif_result_property(result, CHILD_PROPERTY, parent=PARENT_PROPERTY),
    )
    break
else:
    print(f"Missing SARIF {CHILD_PROPERTY}:", EXPECTED)
