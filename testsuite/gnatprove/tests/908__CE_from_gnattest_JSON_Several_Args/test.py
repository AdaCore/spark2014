import os
from test_support import run_spark_for_gnattest_json

run_spark_for_gnattest_json(
    "simple.gpr", "simple.ads", 5, os.path.abspath("JSONs/Several_Args.json")
)
