#!/usr/bin/env python

import argparse
from curses import wrapper
import json
import os
import os.path
import time
from typing import Set, Dict, Tuple
import statistics

descr = """
Run gnatprove with option --why3-logging. Then, run this script, passing the
gnatprove folder to as an argument. If gnatprove is still running, use
`--mode=watch`. If it is finished, use `--mode=batch` (default).
"""


def parse_arguments():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument("logdir", metavar="F", help="directory containing logfiles")
    parser.add_argument(
        "--mode", type=str, help="one of (watch|batch*)", default="batch"
    )
    args = parser.parse_args()
    return args


args = parse_arguments()

report = []


class Goal:
    fn: str
    goalid: int
    status: str
    running_provers: Set[str]
    finished_provers: Dict[str, Tuple[str, float]]

    def __init__(self, fn, g):
        self.fn = fn
        self.goalid = g
        self.status = "unknown"
        self.running_provers = set()
        self.finished_provers = {}

    def process_entry(self, d):
        p = d["prover"]
        if d["pas"]["kind"] == "scheduled":
            assert p not in self.running_provers
            self.running_provers.add(p)
        elif d["pas"]["kind"] == "done":
            assert p in self.running_provers
            self.running_provers.remove(p)
            assert p not in self.finished_provers
            pas = d["pas"]
            answer = pas["answer"]
            self.finished_provers[p] = answer, pas["time"]
            if answer == "valid":
                self.status = "valid"
        else:
            raise ValueError

    def proof_time(self):
        return sum([x[1] for x in self.finished_provers.values()])

    def valid_time(self):
        if self.status == "valid":
            return min(
                [x[1] for x in self.finished_provers.values() if x[0] == "valid"]
            )
        else:
            return None

    def sanity_check(self):
        if self.status == "valid" and len(self.running_provers) > 0:
            report.append(
                (
                    f"in {self.fn}, {self.goalid}: {self.running_provers}",
                    " still running despite valid",
                )
            )
        if self.status == "valid":
            proved_times = [
                x[1] for x in self.finished_provers.values() if x[0] == "valid"
            ]
            mintime_proved = min(proved_times)
            maxtime_proved = max(proved_times)
            maxtime = max([x[1] for x in self.finished_provers.values()])
            if mintime_proved > 30:
                report.append(f"long mintime: {self.finished_provers}")
            if maxtime_proved > 30:
                report.append(f"long maxtime: {self.finished_provers}")
            if maxtime > self.valid_time() + 1:
                report.append(f"maxtime longer than proof: {self.finished_provers}")


class File:
    def __init__(self, logdir, fn):
        self.fn = fn
        self.logdir = logdir
        self.fd = None
        self.data = {}

    def process_entry(self, d):
        g = d["goal_id"]
        if g not in self.data:
            self.data[g] = Goal(self.fn, g)
        assert self.data[g].fn == self.fn
        self.data[g].process_entry(d)

    def scan(self):
        if not self.fd:
            self.fd = open(os.path.join(self.logdir, self.fn), "r")
        while True:
            line = self.fd.readline()
            if not line:
                break
            self.process_entry(json.loads(line))

    def sanity_check(self):
        for v in self.data.values():
            v.sanity_check()

    def valid_times(self):
        return [x.valid_time() for x in self.data.values()]

    def num_goals(self):
        return len(self.data)

    def num_provers(self):
        return sum([len(g.finished_provers) for g in self.data.values()])

    def proof_time(self):
        return sum([x.proof_time() for x in self.data.values()])

    def __hash__(self):
        return hash(self.fn)

    def __eq__(self, other):
        return self.fn == other.fn


files = set()


def scan_files(logdir):
    for f in os.listdir(logdir):
        if f.endswith(".why3log"):
            fobj = File(logdir, f)
            if fobj not in files:
                files.add(fobj)


def show_report(stdscr):
    report.sort()
    stdscr.clear()
    lenreport = len(report)
    maxnum = 10
    stdscr.addstr(0, 0, f"{lenreport} incidents, showing {maxnum} first")
    for i in range(0, min(maxnum, lenreport)):
        stdscr.addstr(i + 1, 0, report[i])
    stdscr.refresh()


def watch(stdscr):
    global report
    while True:
        report = []
        scan_files(args.logdir)
        for v in files:
            v.scan()
        for v in files:
            v.sanity_check()
        show_report(stdscr)
        time.sleep(1)


def main_text():
    args = parse_arguments()
    global report
    while True:
        report = []
        scan_files(args.logdir)
        for v in files:
            v.scan()
        for line in report:
            print(line)
        time.sleep(1)


def batch():
    scan_files(args.logdir)
    for v in files:
        v.scan()
    for v in files:
        v.sanity_check()
    report.sort()
    for line in report:
        print(line)
    stats = [(v.fn, v.num_goals(), v.num_provers(), v.proof_time()) for v in files]
    numgoals = sum([x[1] for x in stats])
    numprovers = sum([x[2] for x in stats])
    prooftime = sum([x[3] for x in stats])
    print(
        f"{len(files)} files with a total of {numgoals} goals",
        f"and {numprovers} provers ({prooftime} s)",
    )
    validtimes = []
    for v in files:
        validtimes += v.valid_times()
    validtimes = [x for x in validtimes if x is not None]
    print(f"mean time of fastest valid proof: {statistics.mean(validtimes)}")
    print(f"quantiles: {[round(q, 1) for q in statistics.quantiles(validtimes, n=10)]}")

    names = {"goals": 1, "provers": 2, "time": 3}
    for key in names.keys():
        print(f"ten largest entrys by {key}")
        stats.sort(key=lambda x: x[names[key]], reverse=True)
        for elt in stats[0:9]:
            print(f"file {elt[0]} with {elt[1]} goals and {elt[2]} provers ({elt[3]}s)")


def main():
    if args.mode == "watch":
        wrapper(watch)
    elif args.mode == "batch":
        batch()
    else:
        print(f"unknown mode {args.mode}")


main()

# wrapper(main)
# main_text()
