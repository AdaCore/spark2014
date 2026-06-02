import json
import os.path
from test_support import prove_all


def check_sarif():
    """Print the originalUriBaseIds keys (sorted) and the uriBaseId and uri
    of the first result that carries a uriBaseId."""
    with open(os.path.join("gnatprove", "gnatprove.sarif")) as f:
        sarif = json.load(f)
    run = sarif["runs"][0]
    for key in sorted(run.get("originalUriBaseIds", {}).keys()):
        print(key)
    for result in run.get("results", []):
        for loc in result.get("locations", []):
            art = loc.get("physicalLocation", {}).get("artifactLocation", {})
            if "uriBaseId" in art:
                print(art["uriBaseId"], art["uri"])
                return


# No --sarif-base-uri: %SRCROOT% must be added automatically
prove_all(no_output=True)
print("=== no switch ===")
check_sarif()

# One custom entry alongside the automatic %SRCROOT%
prove_all(opt=["--sarif-base-uri=MYROOT:/some/path"], no_output=True)
print("=== MYROOT ===")
check_sarif()

# SRCDIR points at the src/ subdirectory: it is a longer match than %SRCROOT%
# so it wins, and the uri becomes the bare filename rather than src/<file>.
prove_all(
    opt=["--sarif-base-uri=SRCDIR:" + os.path.abspath("src")],
    no_output=True,
)
print("=== SRCDIR ===")
check_sarif()

# Explicit %SRCROOT%: no automatic addition on top
prove_all(opt=["--sarif-base-uri=%SRCROOT%:/custom/path"], no_output=True)
print("=== explicit %SRCROOT% ===")
check_sarif()
