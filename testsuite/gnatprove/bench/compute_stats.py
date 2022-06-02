#!/usr/bin/env python
import argparse
import dataclasses
import glob
import json
import os.path
import subprocess
from typing import List
import config

descr = """Compute statistics from json files for provers"""

stats_filename = "stats.txt"
results_filename = "results.json"


# from StackOverflow:
# https://stackoverflow.com/questions/51286748
class EnhancedJSONEncoder(json.JSONEncoder):
    def default(self, o):
        if dataclasses.is_dataclass(o):
            return dataclasses.asdict(o)
        return super().default(o)


def parse_arguments():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument(
        "resultsdir", metavar="R", help="directory which contains proof results"
    )
    parser.add_argument(
        "outdir",
        metavar="O",
        help="directory where results will be stored",
    )
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


def process_test_prover(json_file, testname, provername):
    with open(json_file) as f:
        data = json.load(f)
    for elt in data["results"]:
        status = elt["status"]
        filename = os.path.basename(elt["filename"])
        time = elt["time"] if "time" in elt else 0
        steps = elt["steps"] if "steps" in elt else 0
        if provername not in stats_provers_all:
            stats_provers_all[provername] = Stats()
        if provername not in stats_tests_provers[testname]:
            stats_tests_provers[testname][provername] = Stats()
        for stats_obj in [
            stats_all_vcs,
            stats_provers_all[provername],
            stats_tests_provers[testname][provername],
        ]:
            stats_obj.add_result(testname, filename, provername, status, time, steps)


def process_test(testdir, testname):
    stats_tests_provers[testname] = {}
    for json_file in glob.glob(os.path.join(testdir, "*.json")):
        provername = os.path.splitext(os.path.basename(json_file))[0]
        stats_tests_provers[testname][provername] = Stats()
        process_test_prover(json_file, testname, provername)


def compute_stats(resultsdir):
    dirs = os.listdir(resultsdir)
    for test in dirs:
        mydir = os.path.join(resultsdir, test)
        if not os.path.isdir(mydir):
            continue
        process_test(mydir, test)


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
    assert os.path.exists(args.outdir)
    compute_stats(args.resultsdir)
    with open(os.path.join(args.outdir, stats_filename), "w") as f:
        produce_version_output(f)
        print_stats(f)
    with open(os.path.join(args.outdir, results_filename), "w") as f:
        json.dump(stats_all_vcs.entries, f, cls=EnhancedJSONEncoder)


if __name__ == "__main__":
    main()
