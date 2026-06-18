import os.path
from test_support import first_sarif_artifact_location, prove_all, sarif_run


def print_sarif_base_uri():
    """Print SARIF base-URI information for the current report."""
    run = sarif_run()
    if run is None:
        print("Missing SARIF report")
        return

    print("SARIF originalUriBaseIds:")
    for key in sorted(run.get("originalUriBaseIds", {}).keys()):
        print("  ", key)

    print("SARIF results with 'uriBaseId':")
    artifact = first_sarif_artifact_location(predicate=lambda item: "uriBaseId" in item)
    if artifact is None:
        print("  Missing SARIF artifact location with uriBaseId")
        return

    print(f"  uriBaseId: {artifact["uriBaseId"]}, uri: {artifact["uri"]}")


# No --sarif-base-uri: %SRCROOT% must be added automatically
prove_all(no_output=True)
print("=== no switch ===")
print_sarif_base_uri()

# One custom entry alongside the automatic %SRCROOT%
prove_all(opt=["--sarif-base-uri=MYROOT:/some/path"], no_output=True)
print("=== MYROOT ===")
print_sarif_base_uri()

# SRCDIR points at the src/ subdirectory: it is a longer match than %SRCROOT%
# so it wins, and the uri becomes the bare filename rather than src/<file>.
prove_all(
    opt=["--sarif-base-uri=SRCDIR:" + os.path.abspath("src")],
    no_output=True,
)
print("=== SRCDIR ===")
print_sarif_base_uri()

# Explicit %SRCROOT%: no automatic addition on top
prove_all(opt=["--sarif-base-uri=%SRCROOT%:/custom/path"], no_output=True)
print("=== explicit %SRCROOT% ===")
print_sarif_base_uri()
