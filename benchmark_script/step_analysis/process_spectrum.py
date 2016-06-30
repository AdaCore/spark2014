#!/usr/bin/env python

from common import parse_result
from config import STEP_FLAGS

import os

def load(time):
    INFO = {}

    dn = "spectrum_%u" % time

    for flag in STEP_FLAGS:
        for path, dirs, files in os.walk(os.path.join(dn, "spec_%s" % flag)):
            for f in files:
                x = os.path.splitext(f)[0]
                if x not in INFO:
                    INFO[x] = {}
                INFO[x][flag] = parse_result(os.path.join(path, f))

    totals = {f: 0 for f in STEP_FLAGS}
    n = 0
    all_res = 0
    total_time = 0.0

    for k in INFO:
        is_unknown = False
        is_known   = False
        for f in STEP_FLAGS:
            if INFO[k][f]["status"] == "unknown":
                is_unknown = True
            else:
                is_kown    = True

        assert not (is_known and is_unknown)

        if is_unknown:
            assert not is_known
            n += 1
            for f in STEP_FLAGS:
                totals[f] += INFO[k][f]["resource"]
                all_res   += INFO[k][f]["resource"]
                total_time += INFO[k][f]["time"]

    rps = dict((k, (float(v) / float(n)) / total_time)
               for k, v in totals.iteritems())

    perc = dict((k, float(v * 100) / float(all_res))
                for k, v in totals.iteritems())

    return rps, perc, n

old_rps, old_perc, old_n = load(1000)

def show(t):
    rps, perc, n = load(t)
    print "Spectrum for %.1f seconds (%u samples):" % (float(t) / 1000.0, n)
    for v, k in sorted((v, k) for k, v in perc.iteritems()):
        print "%20s: %.1f (%.1f)" % (k,
                                     v,
                                     v/old_perc.get(k, v))
        #old_rps[k] = v

show(1000)
show(2000)
show(3000)
show(5000)
show(10000)
