#!/usr/bin/env python

# Helper script to detect useless steplimits specified in test.py files.
#
# To make use of this:
#    1. edit test_support.py to override the steplimit by a constant 200
#    2. run the testsuite
#    3. then run this script.

import os
import subprocess


def process(dn):
    p = subprocess.Popen(["git", "diff", dn], stdout=subprocess.PIPE)
    stdout, _ = p.communicate()

    has_diff = len(stdout.strip()) > 0

    if not has_diff:
        print(os.path.join(dn, "test.py"))


for path, _, files in os.walk("tests"):
    for f in files:
        if f == "test.py":
            has_steps = False
            with open(os.path.join(path, f), "rU") as fd:
                tmp = fd.read()
                has_steps = "steps=" in tmp
            if has_steps:
                process(path)
