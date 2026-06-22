import re
from test_support import run_command

# Explain codes that the tool can emit but that knowingly lack an E00NN.md
# explanation file. These are skipped below.
# ??? E0031 (EC_Iterable_Side_Effects) has no explanation file yet; remove it
# from this set once the code is documented or dropped.
KNOWN_MISSING_MD = {"E0031"}

# Get the authoritative, enum-derived list of explain codes from gnatprove
# itself. Because this list comes from the Explain_Code_Kind enumeration, a new
# code is picked up automatically without editing this test.
listing = run_command(["gnatprove", "--debug-list-explain-codes"])
if listing.status != 0:
    print("could not generate the explain codes index:")
    print(listing.out)

codes = sorted(set(re.findall(r"E\d{4}", listing.out)))
if not codes:
    print("no explain codes found in the generated index")

# Every emitted code must have a working '--explain', i.e. an explanation file
# must exist for it. Print nothing on success, so adding a properly documented
# code does not change the expected output; a missing file makes '--explain'
# fail and the test fails.
for code in codes:
    if code in KNOWN_MISSING_MD:
        continue
    result = run_command(["gnatprove", "--explain", code])
    if result.status != 0:
        print(f"gnatprove --explain {code} failed:")
        print(result.out)

# Conversely, an unknown explain code (one past the last known one) must be
# rejected. This exercises the error path of '--explain'.
unknown = f"E{max(int(code[1:]) for code in codes) + 1:04d}"
result = run_command(["gnatprove", "--explain", unknown])
if result.status == 0:
    print(f"gnatprove --explain {unknown} unexpectedly succeeded")
