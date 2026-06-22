from pathlib import Path

from test_support import gnatprove, run_command

# Names of the entities in pkg.ads that are overloaded. A generated entry for
# any of these must carry a profile, otherwise it could not be told apart from
# its sibling overload when the manifest is read back.
OVERLOADED = {"pkg.p", "pkg.f"}


def parse_rules(text):
    """Parse a generated manifest into a list of {key: value} rule dicts."""
    rules = []
    current = None
    for raw in text.splitlines():
        line = raw.strip()
        if line == "[[rule]]":
            current = {}
            rules.append(current)
        elif current is not None and "=" in line and not line.startswith("#"):
            key, _, value = line.partition("=")
            key = key.strip()
            value = value.strip()
            if value.startswith('"') and value.endswith('"'):
                value = value[1:-1]
            current[key] = value
    return rules


print("===== generate manifest =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--mode=prove",
        "--level=0",
        "--generate-manifest-dir=generated",
        "-u",
        "pkg.adb",
    ],
    no_output=True,
)

generated = Path("generated/pkg.toml")
assert generated.is_file()

generated_text = generated.read_text()
assert "[[rule]]" in generated_text
assert "[[subprogram]]" not in generated_text
assert 'path = "Pkg"' in generated_text

print("===== overload invariants =====")
rules = parse_rules(generated_text)

# An explicit entry naming an overloaded subprogram must disambiguate it with a
# profile; otherwise the generated manifest would be ambiguous against itself.
for rule in rules:
    if rule["path"].lower() in OVERLOADED:
        assert rule.get("profile"), rule

# The generator must never emit two entries with the same (path, kind, profile)
# coordinates, which would also be mutually ambiguous when read back.
seen = set()
for rule in rules:
    key = (rule["path"].lower(), rule.get("kind", ""), rule.get("profile", ""))
    assert key not in seen, rule
    seen.add(key)

print("===== round-trip generated manifest =====")
# Reading the generated manifest back on the same overloaded unit must not raise
# any manifest-validity diagnostics: every overload is either covered by a bare
# prefix entry or disambiguated by its own profile.
process = run_command(
    [
        "gnatprove",
        "-f",
        "-P",
        "test.gpr",
        "--mode=prove",
        "--level=0",
        "--proof-manifest-dir=generated",
        "-u",
        "pkg.adb",
    ]
)
assert "invalid proof manifest entry" not in process.out, process.out

print("===== ambiguous overload entry is rejected =====")
# Negative control: a hand-written entry that names an overloaded subprogram
# without a profile is reported as ambiguous. This confirms the round-trip
# check above is meaningful rather than vacuously silent.
ambiguous = Path("ambiguous")
ambiguous.mkdir(exist_ok=True)
(ambiguous / "pkg.toml").write_text(
    """\
version = 1

[[rule]]
path = "Pkg.P"
kind = "procedure"
steps = 100
"""
)
process = run_command(
    [
        "gnatprove",
        "-f",
        "-P",
        "test.gpr",
        "--mode=prove",
        "--level=0",
        "--proof-manifest-dir=ambiguous",
        "-u",
        "pkg.adb",
    ]
)
assert 'for "Pkg.P" kind "procedure" is ambiguous' in process.out, process.out
