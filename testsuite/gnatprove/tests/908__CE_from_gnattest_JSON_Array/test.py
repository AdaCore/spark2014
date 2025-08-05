import os

from test_support import gnatprove


def run_spark(project_file, filename, line, gnattest_JSON):
    gnatprove(
        opt=[
            f"-P{project_file}",
            "--quiet",
            "--output=oneline",
            "--counterexamples=on",
            "--check-counterexamples=on",
            "--level=2",
            f"--limit-subp={filename}:{line}",
            f"--gnattest-values={gnattest_JSON}",
        ]
    )


run_spark("simple.gpr", "simple.ads", 11, os.path.abspath("JSONs/Add_Array.json"))

run_spark("simple.gpr", "simple.ads", 23, os.path.abspath("JSONs/Check_Family.json"))
