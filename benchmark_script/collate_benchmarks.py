#!/usr/bin/env python

import os
import sys
import shutil

bm = {}

for path, dirs, files in os.walk("data"):
    for f in files:
        if f.endswith(".smt2") or f.endswith(".why"):
            # Strip extension and trailing numbers added by why3
            vc_name = f.rsplit(".", 1)[0].rstrip("0123456789")

            # Chop off prefix
            test_name = path[len("data/tmp-test-"):]
            # Chop rest of the path
            test_name = test_name.split("/", 1)[0]
            # Chop the number suffix
            test_name = test_name.rsplit("-", 1)[0]

            name = test_name + "__" + vc_name
            name = name.replace(" ", "_")

            if f.endswith(".smt2"):
                prover = "cvc4"
            else:
                prover = "altergo"

            if name not in bm:
                bm[name] = {prover: os.path.join(path, f)}
            else:
                bm[name][prover] = os.path.join(path, f)

ignored = []
for test in bm:
    if len(bm[test]) != 2:
        print "Ignoring test %s without comparison results..." % test
        ignored.append(test)

for i in ignored:
    del bm[i]

PROVERS = ["cvc4", "altergo"]

EXT = {
    "cvc4":    "smt2",
    "altergo": "why"
}

for p in PROVERS:
    os.makedirs(os.path.join("bench", p))

for test in bm:
    for p in PROVERS:
        dst = os.path.join("bench", p, test + "." + EXT[p])
        assert (not os.path.exists(dst))
        shutil.copyfile(bm[test][p], dst)
