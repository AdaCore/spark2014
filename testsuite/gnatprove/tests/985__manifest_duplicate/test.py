import os

from test_support import gnatprove

# The two manifest files below differ only in case ("Main.toml" vs
# "main.toml"). They are generated here rather than stored in the repository so
# that they do not appear as spuriously modified when checked out on a
# case-insensitive file system. The accompanying test.opt skips this test on
# such systems, so the files are never created there.

os.mkdir("duplicate_unit_manifest")

with open(os.path.join("duplicate_unit_manifest", "Main.toml"), "w") as f:
    f.write(
        """version = 1

[[subprogram]]
path = "Main"
kind = "procedure"
level = 2
"""
    )

with open(os.path.join("duplicate_unit_manifest", "main.toml"), "w") as f:
    f.write(
        """version = 1

[[subprogram]]
path = "Main.Inner"
kind = "procedure"
level = 1
"""
    )

gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=duplicate_unit_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)
