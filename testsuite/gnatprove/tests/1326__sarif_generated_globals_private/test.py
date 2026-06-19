import json
from glob import glob

from test_support import (
    find_sarif_logical_locations,
    prove_all,
    sarif_logical_location_property,
)

PARENT_PROPERTY = "gnatprove"
CHILD_PROPERTY = "inferredContracts"


def print_contract(name):
    for item in find_sarif_logical_locations(fully_qualified_name=name):
        print("SARIF logicalLocation:", name)
        print("SARIF logicalLocation name:", item["name"])
        print(
            json.dumps(
                sarif_logical_location_property(
                    item, CHILD_PROPERTY, parent=PARENT_PROPERTY
                ),
                sort_keys=True,
                indent=2,
            )
        )
        break
    else:
        print("Missing SARIF logicalLocation:", name)


def print_spark_contract(name):
    for spark_file in sorted(glob("gnatprove/*.spark")):
        with open(spark_file) as file:
            data = json.load(file)
        for entity_key, entity in data["entities"].items():
            if entity["name"] == name:
                print("SPARK generated_globals:", name)
                print(
                    json.dumps(
                        data["generated_globals"][entity_key],
                        sort_keys=True,
                        indent=2,
                    )
                )
                return
    print("Missing .spark generated_globals:", name)


prove_all(
    opt=["--flow-show-gg", "--no-inlining"],
    steps=1,
    counterexample=False,
    prover=["cvc5"],
    no_output=True,
)

print_spark_contract("A.P_1")
print_spark_contract("A.Priv.F_6")
print_contract("A.P_1")
print_contract("A.Priv.F_6")
