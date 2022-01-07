#!/usr/bin/env python

""" A small script to check how a change to the proof system affects the
    number of discharged VCs.

    Usage: git diff | ./analyze_diff.py
"""

import sys

proved = 0
failed = 0

for raw_line in sys.stdin:
    if len(raw_line) < 2:
        continue
    if raw_line[0] == "-":
        val = -1
    elif raw_line[0] == "+":
        val = 1
    else:
        continue
    if raw_line[1] in ("+", "-"):
        continue
    if ".ad" not in raw_line:
        continue

    if " proved" in raw_line or "postcondition is stronger" in raw_line:
        proved += val
    elif " might " in raw_line or "precondition is stronger" in raw_line:
        failed += val
    else:
        print(raw_line.rstrip())

print("Proved: %i" % proved)
print("Failed: %i" % failed)
