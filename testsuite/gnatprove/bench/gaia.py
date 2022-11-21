#!/usr/bin/env python

import argparse
import config
import e3.yaml
import json
import os.path
import shutil
import subprocess

descr = """
The main argument is a json file which contains all the prover results.
The script generates files in the same dir as the argument file, which can be
interpreted by GAIA as testsuite results.
"""


def parse_arguments():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument(
        "resultfile",
        metavar="F",
        help="JSON file that contains all results",
    )
    parser.add_argument(
        "--testsuite-dir",
        type=str,
        default=None,
        required=True,
        help="directory which contains the testsuite",
    )
    args = parser.parse_args()
    return args


def load_baseline(outdir, testsuitedir, testname):
    baseline_file = os.path.join(testsuitedir, "tests", testname, "bench.yaml")
    if os.path.exists(baseline_file):
        baseline = e3.yaml.load_with_config(baseline_file, {})
        shutil.copyfile(baseline_file, os.path.join(outdir, testname + ".expected"))
    else:
        baseline = {}
    for prover in config.all_provers:
        if prover not in baseline:
            baseline[prover] = 100
    return baseline


def compare_baseline(n, data, prover, fn):
    """n is a percentage (integer). results is a list of all results. We check
    that unsat is at least percentage expressed by n.
    """
    local_data = [x for x in data if x["prover"] == prover]
    total = len(local_data)
    unsat = len([x for x in local_data if x["status"] == "unsat"])
    if total == 0:
        fn.write("VC count for " + prover + " is 0\n")
        return False
    percent = unsat * 100 // total
    if percent < n:
        fn.write(
            f"{prover} proved {unsat} out of {total} VCs"
            + f"({percent}%), but {n}% was required.\n"
        )
        return False
    else:
        return True


def compute_test_status(testsuitedir, outdir, test, data, resultfile):
    baseline = load_baseline(outdir, testsuitedir, test)
    res = True
    with open(os.path.join(outdir, test + ".diff"), "w") as diff_fn:
        for prover in config.all_provers:
            res = compare_baseline(baseline[prover], data, prover, diff_fn) and res
    if res:
        resultfile.write(test + ":OK\n")
    else:
        resultfile.write(test + ":DIFF\n")


def compute_stat_count(data):
    keys = {x["status"] for x in data}
    result = {}
    for elt in keys:
        result[elt] = sum(x["status"] == elt for x in data)
    return result


def compute_results(data, outdir, testsuitedir, resultfile):
    alltests = {x["testname"] for x in data}
    for test in alltests:
        testdata = [x for x in data if x["testname"] == test]
        with open(os.path.join(outdir, test + ".out"), "w") as f:
            for p in config.all_provers:
                f.write(p + ":")
                f.write(str(compute_stat_count(testdata)))
                f.write("\n")
        compute_test_status(testsuitedir, outdir, test, testdata, resultfile)


def produce_version_output(outdir, resultfile):
    resultfile.write("version:XFAIL:always fails\n")
    with open(os.path.join(outdir, "version.out"), "w") as f:
        for p in config.all_provers:
            exec_name = "alt-ergo" if p == "altergo" else p
            f.write(subprocess.check_output([exec_name, "--version"]).decode("utf-8"))


def main():
    args = parse_arguments()
    with open(args.resultfile, "r") as f:
        data = json.load(f)
    outdir = os.path.dirname(args.resultfile)
    results_file = os.path.join(outdir, "results")
    with open(results_file, "w") as f:
        produce_version_output(outdir, f)
        compute_results(data["results"], outdir, args.testsuite_dir, f)


if __name__ == "__main__":
    main()
