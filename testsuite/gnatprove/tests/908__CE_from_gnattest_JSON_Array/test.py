import os
from test_support import run_spark_for_gnattest_json


run_spark_for_gnattest_json(
    "simple.gpr", "simple.ads", 11, os.path.abspath("JSONs/Add_Array.json")
)

run_spark_for_gnattest_json(
    "simple.gpr", "simple.ads", 23, os.path.abspath("JSONs/Check_Family.json")
)
