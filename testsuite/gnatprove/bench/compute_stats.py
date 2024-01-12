#!/usr/bin/env python
import argparse
import dataclasses
import json
import os.path
import subprocess
import sys
from typing import List
import config

descr = """Compute statistics from json files for provers"""


class EnhancedJSONEncoder(json.JSONEncoder):
    def default(self, o):
        if dataclasses.is_dataclass(o):
            return dataclasses.asdict(o)
        return super().default(o)


def parse_arguments():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument("json_report", metavar="R", help="file contains proof results")
    args = parser.parse_args()
    return args


def produce_version_output(f):
    for p in config.all_provers:
        exec_name = "alt-ergo" if p == "altergo" else p
        f.write(subprocess.check_output([exec_name, "--version"]).decode("utf-8"))


@dataclasses.dataclass
class Entry:
    testname: str
    filename: str
    prover: str
    time: float
    steps: int
    status: str


class Stats:
    def __init__(self):
        self.status_count = {}
        self.proved_entries_time = []
        self.proved_entries_steps = []
        self.proved_entries_stats = []
        self.entries: List[Entry] = []

    def add_result(self, testname, filename, prover, status, time, steps):
        """add single result to stats object"""
        self.entries.append(Entry(testname, filename, prover, time, steps, status))
        if status not in self.status_count:
            self.status_count[status] = 0
        self.status_count[status] += 1
        if status == "unsat":
            self.proved_entries_time.append(time)
            self.proved_entries_steps.append(steps)

    def get_threshold_list(self, entries_list):
        """compute statistics over all results"""
        total = len(entries_list)
        if total == 0:
            return []
        entries_list.sort()
        thresholds = {}
        count = 1
        for i in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]:
            while count / total < i:
                count += 1
            thresholds[i] = entries_list[count - 1]
        return thresholds

    def print_stats(self, f):
        f.write(str(self.status_count) + "\n")
        f.write("Time/Steps needed to prove x % of all proved VCS:\n")
        f.write(str(self.get_threshold_list(self.proved_entries_time)) + "\n")
        f.write(str(self.get_threshold_list(self.proved_entries_steps)) + "\n")


stats_all_vcs = Stats()

stats_provers_all = {}

stats_tests_provers = {}


def process_item(elt):
    global stats_tests_provers, stats_provers_all, stats_all_vcs
    status = elt["status"]
    filename = os.path.basename(elt["filename"])
    time = elt["time"] if "time" in elt else 0
    steps = elt["steps"] if "steps" in elt else 0
    testname = elt["testname"]
    provername = elt["prover"]
    if provername not in stats_provers_all:
        stats_provers_all[provername] = Stats()
    if testname not in stats_tests_provers:
        stats_tests_provers[testname] = {}
    if provername not in stats_tests_provers[testname]:
        stats_tests_provers[testname][provername] = Stats()
    for stats_obj in [
        stats_all_vcs,
        stats_provers_all[provername],
        stats_tests_provers[testname][provername],
    ]:
        stats_obj.add_result(testname, filename, provername, status, time, steps)


def print_stats(f):
    f.write("Statistics for all provers and all tests:\n")
    stats_all_vcs.print_stats(f)
    f.write("Statistics for each prover over all tests:\n")
    for p in stats_provers_all.keys():
        f.write(p + "\n")
        stats_provers_all[p].print_stats(f)
    f.write("Statistics for each prover for each test:\n")
    for test, m in stats_tests_provers.items():
        f.write("Statistics for test " + test + "\n")
        for p, statobj in m.items():
            f.write(p + "\n")
            statobj.print_stats(f)


def main():
    args = parse_arguments()
    with open(args.json_report, "r") as f:
        data = json.load(f)
    for item in data["results"]:
        process_item(item)
    print_stats(sys.stdout)


if __name__ == "__main__":
    main()
