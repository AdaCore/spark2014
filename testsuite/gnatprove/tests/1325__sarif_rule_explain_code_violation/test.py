from test_support import (
    capture_prove_all,
    find_sarif_rules,
    find_sarif_results,
    sarif_rule_property,
    sarif_result_property,
)

EXPLAIN_CODE = "E0006"
COMMAND = f"gnatprove --explain={EXPLAIN_CODE}"
PARENT_PROPERTY = "gnatprove"
EXPLAIN_CODE_PROPERTY = "explainCode"
EXPLAIN_COMMAND_PROPERTY = "explainCommand"
RULE_ID = "violation-volatile-global"

output = capture_prove_all()

if f"[{EXPLAIN_CODE}]" not in output:
    print("Missing CLI explainCode:", EXPLAIN_CODE)
else:
    print("CLI explainCode:", EXPLAIN_CODE)

for result in find_sarif_results(
    rule_id=RULE_ID,
    predicate=lambda item: (
        sarif_result_property(item, EXPLAIN_CODE_PROPERTY, PARENT_PROPERTY)
        == EXPLAIN_CODE
    ),
):
    print(
        "SARIF explainCode:",
        sarif_result_property(result, EXPLAIN_CODE_PROPERTY, PARENT_PROPERTY),
    )
    print(
        "SARIF explainCommand:",
        sarif_result_property(result, EXPLAIN_COMMAND_PROPERTY, PARENT_PROPERTY),
    )
    break
else:
    print("Missing SARIF explainCode:", EXPLAIN_CODE)
    print("Missing SARIF explainCommand:", COMMAND)

for rule in find_sarif_rules(
    rule_id=RULE_ID,
    predicate=lambda item: (
        sarif_rule_property(item, EXPLAIN_CODE_PROPERTY, PARENT_PROPERTY)
        == EXPLAIN_CODE
    ),
):
    print(
        "SARIF rule explainCode:",
        sarif_rule_property(rule, EXPLAIN_CODE_PROPERTY, PARENT_PROPERTY),
    )
    print(
        "SARIF rule explainCommand:",
        sarif_rule_property(rule, EXPLAIN_COMMAND_PROPERTY, PARENT_PROPERTY),
    )
    break
else:
    print("Missing SARIF rule explainCode:", EXPLAIN_CODE)
    print("Missing SARIF rule explainCommand:", COMMAND)
