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


run_spark("simple.gpr", "simple.ads", 13, os.path.abspath("JSONs/Sum_People.json"))

run_spark("simple.gpr", "simple.ads", 22, os.path.abspath("JSONs/Check_Town.json"))

run_spark("simple.gpr", "simple.ads", 30, os.path.abspath("JSONs/Check_Record.json"))
