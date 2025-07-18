import os
import subprocess


def run_spark(project_file, filename, line, gnattest_JSON):
    print("Running gnatprove")
    subprocess.run(
        [
            "gnatprove",
            f"-P{project_file}",
            "-j0",
            "--output=oneline",
            "--counterexamples=on",
            "--check-counterexamples=on",
            "--level=2",
            f"--limit-subp={filename}:{line}",
            f"--gnattest-values={gnattest_JSON}",
        ]
    )


run_spark("simple.gpr", "simple.ads", 15, os.path.abspath("JSONs/Foo.json"))

run_spark("simple.gpr", "simple.ads", 18, os.path.abspath("JSONs/Bar.json"))

run_spark("simple.gpr", "simple.ads", 21, os.path.abspath("JSONs/Sum_People.json"))

run_spark("simple.gpr", "simple.ads", 23, os.path.abspath("JSONs/Div_Float.json"))

run_spark("simple.gpr", "simple.ads", 29, os.path.abspath("JSONs/Add_Array.json"))

run_spark("simple.gpr", "simple.ads", 31, os.path.abspath("JSONs/Nested_CE.json"))

run_spark("simple.gpr", "simple.ads", 41, os.path.abspath("JSONs/Check_Town.json"))

run_spark("simple.gpr", "simple.ads", 45, os.path.abspath("JSONs/Mammals.json"))

run_spark("simple.gpr", "simple.ads", 47, os.path.abspath("JSONs/Not_Michel.json"))

run_spark("simple.gpr", "simple.ads", 51, os.path.abspath("JSONs/Check_Family.json"))

run_spark("simple.gpr", "simple.ads", 55, os.path.abspath("JSONs/Sum_List.json"))

run_spark("simple.gpr", "simple.ads", 75, os.path.abspath("JSONs/Test_Shape.json"))

run_spark("simple.gpr", "simple.ads", 83, os.path.abspath("JSONs/Check_Record.json"))

run_spark("simple.gpr", "simple.ads", 85, os.path.abspath("JSONs/Several_Args.json"))
