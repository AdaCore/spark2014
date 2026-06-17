from test_support import gnatprove


print("===== valid manifest =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=valid_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ],
    no_output=True,
)

print("===== unit and package manifest =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=unit_and_package_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ],
    no_output=True,
)

print("===== unit and nested package manifest =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=unit_and_nested_package_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ],
    no_output=True,
)

print("===== unknown field =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=unknown_field_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== bad provers syntax =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=bad_provers_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== missing path =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=missing_path_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== missing version =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=missing_version_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== unsupported version =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=unsupported_version_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== missing folder =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=missing_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== file instead of folder =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=main.adb",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== wrong unit =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=wrong_unit_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== bad kind =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=bad_kind_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== profile without kind =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=profile_without_kind_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== bad hierarchical =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=unit_profile_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== package profile =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=package_profile_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== no options =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=no_options_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== bad level =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=bad_level_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== duplicate entry =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=duplicate_entry_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== duplicate prover =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=duplicate_prover_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== bad path =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=bad_path_manifest",
        "--mode=check",
        "-u",
        "main.adb",
    ]
)

print("===== project switch rejected =====")
gnatprove(opt=["-P", "manifest_in_project.gpr", "--mode=check", "-u", "main.adb"])
