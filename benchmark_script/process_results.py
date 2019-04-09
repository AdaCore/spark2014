#!/usr/bin/env python

import os
import sys

tests = set()

PROVERS = ["altergo"]

EXT = {
    "altergo": "why",
    "cvc4_16": "smt2",
    "z3_gnatprove": "smt2",
    "z3_gnatprove_ce":  "smt2",
}

VERDICTS = {
    "cvc4_16": {"sat":     ["sat"],
                "unsat":   ["unsat"],
                "unknown": ["unknown"]},
    "z3_gnatprove": {"sat":     ["sat"],
               "unsat":   ["unsat"],
               "unknown": ["unknown",
                           "number of configured allocations exceeded",
                           "Segmentation fault",
                           "Aborted"]},
    "z3_gnatprove_ce": {"sat":     ["sat"],
               "unsat":   ["unsat"],
               "unknown": ["unknown",
                           "number of configured allocations exceeded",
                           "Segmentation fault",
                           "Aborted"]},
    "altergo": {"sat":     ["Invalid"],
                "unsat":   ["Valid"],
                "unknown": ["I don't know", "Timeout"]},
}

# Obtain set of tests (we trust we have one for each prover since
# collate_benchmarks checks for that...
for path, paths, files in os.walk("bench"):
    for f in files:
        # Chop extension
        root_name = f.rsplit(".", 1)[0]
        tests.add(root_name)

# Process results (and make sure we have results for everything)
results = {}
for t in tests:
    for p in PROVERS:
        base = os.path.join("bench", p, t + ".")
        if not os.path.isfile(base + EXT[p]):
            print "Benchmark does not exist: " + base + EXT[p]
            sys.exit(1)
        if not os.path.isfile(base + "result"):
            print "Result does not exist: " + base + "result"
            sys.exit(1)

        if t not in results:
            results[t] = {}

        with open(base + "result", "rU") as fd:
            tmp = fd.read().strip()
        verdict = None
        for v in ["unsat", "sat", "unknown"]:
            for verd in VERDICTS[p][v]:
                if verd in tmp:
                    verdict = v
                    break
            if verdict is not None:
                break
        assert verdict is not None

        results[t][p] = verdict

# Select tests we're interested in...
# for t in results:
#     if results[t]["altergo"] == "unsat":
#         if results[t]["cvc4"] != "unsat":
#             print t

total_vcs = len(results)
total_decision = 0
time_min = None
time_max = None
time_total = 0.0
for t in results:
    if results[t]["z3_432"] in ("unsat", "sat"):
        total_decision += 1

print "VCs: %u / %u (%.1f%%)" % (total_decision,
                                 total_vcs,
                                 float(total_decision*100) / float(total_vcs))
