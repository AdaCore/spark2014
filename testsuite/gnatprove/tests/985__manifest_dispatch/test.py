from test_support import gnatprove


print("===== resolved manifest entry =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=resolved",
        "-u",
        "pkg.adb",
    ],
    no_output=True,
)

print("===== ambiguous manifest entry =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=ambiguous",
        "-u",
        "pkg.adb",
    ]
)

print("===== missing manifest entity =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=missing_entity",
        "-u",
        "pkg.adb",
    ]
)

print("===== manifest entity not selected =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=not_selected",
        "--limit-name=P",
        "-u",
        "pkg.adb",
    ]
)

print("===== manifest applies steps override =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=apply_steps",
        "--report=all",
        "--limit-name=R",
        "-u",
        "pkg.adb",
    ]
)

print("===== package prefix covers multiple subprograms =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=pkg_prefix",
        "-u",
        "pkg.adb",
    ],
    no_output=True,
)

print("===== nested prefix covers single subprogram =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=inner_prefix",
        "-u",
        "pkg.adb",
    ],
    no_output=True,
)

print("===== specific entry overrides broader entry =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=override",
        "-u",
        "pkg.adb",
    ],
    no_output=True,
)

print("===== two same-specificity entries are ambiguous =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=tie_ambiguity",
        "-u",
        "pkg.adb",
    ]
)
