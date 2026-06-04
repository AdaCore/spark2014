import os
from test_support import default_refiners_no_sort, run_spark_for_gnattest_json


run_spark_for_gnattest_json(
    "simple.gpr",
    "simple.ads",
    7,
    os.path.abspath("JSONs/Foo.json"),
    refiners=default_refiners_no_sort(),
)
