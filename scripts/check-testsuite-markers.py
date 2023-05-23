from pathlib import Path
import sys

# This script fails if a file in argument that ends with ".out" contains
# undesirable text.

undesirable_messages = [
    "SOUNDNESS BUG",
    "PROOF REGRESSION",
    "SPURIOUS MESSAGE",
    "FAILED CHECK UNEXPECTED",
]


def check_contains_undesirable(p):
    with open(p, "r") as f:
        out = f.read()
    for msg in undesirable_messages:
        if msg in out:
            print(f"file {p} contains text '{msg}'; remove before committing")
            exit(1)


if __name__ == "__main__":
    for f in sys.argv:
        p = Path(f)
        if p.suffix == ".out":
            check_contains_undesirable(p)
