#!/usr/bin/env python

def parse_result(fn):
    rv = {"status"   : None,
          "resource" : None,
          "time"     : None}

    with open(fn, "rU") as fd:
        for raw_line in fd:
            key, raw_value = raw_line.strip().split(",", 1)
            raw_value = raw_value.strip()

            if key == "driver::sat/unsat":
                rv["status"] = raw_value.split()[0]
                assert rv["status"] in set(["unsat",
                                            "sat",
                                            "unknown"])

            elif key == "smt::SmtEngine::resourceUnitsUsed":
                rv["resource"] = int(raw_value)

            elif key == "driver::totalTime":
                rv["time"] = float(raw_value)

    if None in list(rv.itervalues()):
        print "error processing", fn

    return rv
