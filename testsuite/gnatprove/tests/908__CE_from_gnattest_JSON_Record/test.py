import os
from test_support import run_spark_for_gnattest_json


run_spark_for_gnattest_json(
    "simple.gpr", "simple.ads", 13, os.path.abspath("JSONs/Sum_People.json")
)

run_spark_for_gnattest_json(
    "simple.gpr", "simple.ads", 22, os.path.abspath("JSONs/Check_Town.json")
)

run_spark_for_gnattest_json(
    "simple.gpr", "simple.ads", 30, os.path.abspath("JSONs/Check_Record.json")
)
