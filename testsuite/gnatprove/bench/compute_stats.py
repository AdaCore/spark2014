#!/usr/bin/env python
import argparse
import json
import os.path
import subprocess
import config

descr = """Compute statistics from json files for provers"""


def parse_arguments():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument(
        "resultsdir", metavar="F", help="directory which contains proof results"
    )
    parser.add_argument(
        "outdir",
        metavar="F",
        help="directory where results/diffs for GAIA will be stored",
    )
    args = parser.parse_args()
    return args


def produce_version_output(f):
    for p in config.all_provers:
        exec_name = "alt-ergo" if p == "altergo" else p
        f.write(subprocess.check_output([exec_name, "--version"]).decode("utf-8"))


class Stats:
    def __init__(self):
        self.status_count = {}
        self.proved_entries_time = []
        self.proved_entries_steps = []
        self.proved_entries_stats = []

    def add_result(self, status, time, steps):
        """add single result to stats object"""
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
for p in config.all_provers:
    stats_provers_all[p] = Stats()

stats_tests_provers = {}


def process_test_prover(json_file, testname, provername):
    with open(json_file) as f:
        data = json.load(f)
    for elt in data["results"]:
        status = elt["status"]
        time = elt["time"] if "time" in elt else 0
        steps = elt["steps"] if "steps" in elt else 0
        for stats_obj in [
            stats_all_vcs,
            stats_provers_all[provername],
            stats_tests_provers[testname][provername],
        ]:
            stats_obj.add_result(status, time, steps)


def process_test(testdir, testname):
    stats_tests_provers[testname] = {}
    for p in config.all_provers:
        json_file = os.path.join(testdir, p + ".json")
        stats_tests_provers[testname][p] = Stats()
        process_test_prover(json_file, testname, p)


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
    for p in config.all_provers:
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
    outfile = os.path.join(args.outdir, "stats.txt")
    compute_stats(args.resultsdir)
    with open(outfile, "w") as f:
        produce_version_output(f)
        print_stats(f)


if __name__ == "__main__":
    main()
