import os
from test_support import default_refiners_no_sort, run_spark_for_gnattest_json

run_spark_for_gnattest_json(
    "simple.gpr",
    "simple.ads",
    11,
    os.path.abspath("JSONs/Add_Array.json"),
    refiners=default_refiners_no_sort(),
)

run_spark_for_gnattest_json(
    "simple.gpr",
    "simple.ads",
    23,
    os.path.abspath("JSONs/Check_Family.json"),
    refiners=default_refiners_no_sort(),
)
