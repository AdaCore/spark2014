#!/usr/bin/env python

from common import *
from config import STEPS, TIMES

import os

def process(root):
    INFO = {}

    def process_dir(rd):
        for path, dirs, files in os.walk(os.path.join(root, rd)):
            for f in files:
                if f not in INFO:
                    INFO[f] = {}

                INFO[f][rd] = parse_result(os.path.join(path, f))

    for t in STEPS:
        process_dir("res_%u" % t)
    for t in TIMES:
        process_dir("tim_%u" % t)

    results = ["res_%u" % x for x in STEPS] + ["tim_%u" % x for x in TIMES]

    rv = {}

    for rd in results:
        total_res = 0
        total_files = 0
        total_time = 0.0
        total_solved = 0
        time_solved = 0.0
        for x in INFO:
            f = INFO[x][rd]

            total_res   += f["resource"]
            total_time  += f["time"]
            total_files += 1
            if f["status"] == "unsat":
                total_solved += 1
                time_solved  += f["resource"]
        avg_steps = float(total_res) / float(total_files)
        avg_steps_second = avg_steps / total_time

        rv[rd] = {"avg_steps"  : avg_steps,
                  "avg_rps"    : avg_steps_second,
                  "solved"     : total_solved,
                  "solved_pct" : float(total_solved) / float(len(INFO)) * 100.0,
                  "total_time" : total_time,
                  "avg_time"   : total_time / float(len(INFO)),
                  "avg_solve"  : time_solved / float(total_solved)}
    return rv

data = [
    {"name" : "Baseline",
     "data" : process("baseline")},

    # {"name" : "Old flags",
    #  "data" : process("oldflags")},

    {"name" : "New flags",
     "data" : process("newflags")},

    {"name" : "New flags B",
     "data" : process("newflags_b")},
]

with open("gp", "w") as fd:
    fd.write("set terminal pdfcairo dashed\n")
    fd.write("set output \"plot.pdf\"\n")
    fd.write("set autoscale y\n")
    fd.write("set autoscale y2\n")
    fd.write("set logscale x 10\n")
    fd.write("set xlabel '--steps'\n")
    fd.write("set x2label 'seconds'\n")
    fd.write("set ylabel 'solved'\n")
    fd.write("set y2label 'avg time'\n")
    fd.write("set x2tics\n")
    fd.write("set y2tics\n")
    fd.write("set key below\n")

    base = "'-' using 1:2"
    kind = "with linespoints"

    plots = []
    n = 0
    for itm in data:
        n += 1
        plots.append("%s axes x1y1 %s lc %u lt 1 title '%s (r)'" % (base,
                                                                kind,
                                                                n,
                                                                itm["name"]))
        plots.append("%s axes x1y2 %s lc %u lt 2 title 'time'" % (base,
                                                                  kind,
                                                                  n))
        plots.append("%s axes x2y1 %s lc %u lt 3 title '%s (s)'" % (base,
                                                                    kind,
                                                                    n,
                                                                    itm["name"]))
    fd.write("plot %s\n" % ", ".join(plots))

    for itm in data:
        for t in STEPS:
            fd.write("%u %.3f\n" % (t, itm["data"]["res_%u" % t]["solved"]))
        fd.write("e\n")
        for t in STEPS:
            fd.write("%u %.3f\n" % (t, itm["data"]["res_%u" % t]["total_time"]))
        fd.write("e\n")
        for t in TIMES:
            fd.write("%0.1f %.3f\n" % (t / 1000.0, itm["data"]["tim_%u" % t]["solved"]))
        fd.write("e\n")

os.system("gnuplot gp")
