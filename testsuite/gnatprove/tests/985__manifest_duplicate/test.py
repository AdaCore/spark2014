from test_support import gnatprove

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
