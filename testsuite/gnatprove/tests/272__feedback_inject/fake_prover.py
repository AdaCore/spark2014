#!/usr/bin/env python3
"""Fake prover for testing prover feedback.

It ignores the verification condition it is given and simply prints a marker
line that the companion driver (fake.drv) maps to a specific prover answer.
The marker to print is selected by the first command-line argument.
"""

import sys

MARKERS = {
    "gaveup": "GNATPROVE_FAKE_GAVEUP",
    "timeout": "GNATPROVE_FAKE_TIMEOUT",
    "steplimit": "GNATPROVE_FAKE_STEPLIMIT",
    "outofmemory": "GNATPROVE_FAKE_OUTOFMEMORY",
}

if __name__ == "__main__":
    print(MARKERS[sys.argv[1]])
