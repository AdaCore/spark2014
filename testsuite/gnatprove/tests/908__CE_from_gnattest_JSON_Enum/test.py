import os
from test_support import run_spark_for_gnattest_json


run_spark_for_gnattest_json(
    "simple.gpr", "simple.ads", 7, os.path.abspath("JSONs/Mammals.json")
)
