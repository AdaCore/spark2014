import json
import os

from test_support import run_command

manifest_dir = "manifest"
os.makedirs(manifest_dir, exist_ok=True)

with open(os.path.join(manifest_dir, "pkg.toml"), "w") as f:
    f.write(
        """\
version = 1

[[rule]]
path = "Pkg.Box.Set"
kind = "entry"
profile = "(_ : Integer)"
steps = 123
"""
    )

process = run_command(
    [
        "gnatprove",
        "-k",
        "-P",
        "test.gpr",
        "--debug",
        f"--proof-manifest-dir={manifest_dir}",
        "-u",
        "pkg.adb",
        "--output=brief",
    ]
)

gnatwhy3_lines = [
    line for line in process.out.splitlines() if line.startswith("gnatwhy3 ")
]
matching_lines = [line for line in gnatwhy3_lines if " --steps 123 " in f" {line} "]

if len(matching_lines) != 1:
    raise AssertionError(process.out)

with open(os.path.join("gnatprove", "pkg.spark")) as f:
    spark_data = json.load(f)

for entity in spark_data["entities"].values():
    if entity["name"] == "Pkg.Box.Set":
        if entity.get("manifest_kind") != "entry":
            raise AssertionError(entity)
        if entity.get("manifest_profile") != "(_ : Integer)":
            raise AssertionError(entity)
        break
else:
    raise AssertionError(spark_data["entities"])
