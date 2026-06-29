import os

from test_support import gnatprove

# Prove a simple VC with cvc5 into a file-based proof cache, then inspect the
# cvc5 result files left in the cache directory. cvc5 is invoked with
# --stats-internal, which dumps many noisy statistics; the memcached wrapper is
# expected to filter all of them out of the cache except the
# resource::resourceUnitsUsed line that gnatwhy3 consumes to count proof steps.
# This is a regression test for the cvc5 statistics polluting the proof cache.

CACHE = os.path.abspath("cache")
os.makedirs(CACHE, exist_ok=True)

gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--prover=cvc5",
        "--counterexamples=off",
        "--check-counterexamples=off",
        f"--memcached-server=file:{CACHE}",
    ],
    cache_allowed=False,
    no_output=True,
)

# cvc5 result files in the cache start with a sat/unsat/unknown verdict, as
# opposed to the gnatwhy3 result files, which hold JSON. For each such file,
# check that the only "::"-namespaced statistic kept is resourceUnitsUsed.

VERDICTS = {"sat", "unsat", "unknown"}
RESOURCE = "resource::resourceUnitsUsed = "
checked = 0

for name in sorted(os.listdir(CACHE)):
    with open(os.path.join(CACHE, name), encoding="utf-8") as cache_file:
        lines = cache_file.read().splitlines()

    if not lines or lines[0] not in VERDICTS:
        continue

    checked += 1

    leaked = [line for line in lines if "::" in line and not line.startswith(RESOURCE)]
    if leaked:
        print(f"leaked statistics in cvc5 cache file: {leaked}")

    if not any(line.startswith(RESOURCE) for line in lines):
        print("missing resource::resourceUnitsUsed line in cvc5 cache file")

if checked == 0:
    print("no cvc5 cache files found")
else:
    print("OK: cvc5 cache files keep only the verdict and the resource statistic")
