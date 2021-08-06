#!/usr/bin/env python

import argparse
import e3.yaml
import json
import os.path
import shutil
import subprocess

descr = """Compute results from json files for provers"""

all_provers = ["cvc4", "altergo", "z3"]


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
    parser.add_argument(
        "--testsuite-dir",
        type=str,
        default=None,
        required=True,
        help="directory which contains the testsuite",
    )
    args = parser.parse_args()
    return args


def compute_stat_count(fn):
    results = {"unsat": 0}
    with open(fn) as f:
        data = json.load(f)
    for elt in data["results"]:
        status = elt["status"]
        if status not in results:
            results[status] = 0
        results[status] += 1
    return results


def compare_baseline(n, results, prover, fn):
    """n is a percentage (integer). results is a dictionary that maps prover
    status to count. We check that unsat is at least percentage expressed by
    n.
    """
    total = 0
    for s in results.values():
        total += s
    if total == 0:
        fn.write("VC count for " + prover + " is 0\n")
        return False
    percent = results["unsat"] * 100 // total
    if percent < n:
        fn.write(
            f"{prover} proved {results['unsat']} out of {total} VCs"
            + f"({percent}%), but {n}% was required.\n"
        )
        return False
    else:
        return True


def compute_test_status(testsuitedir, outdir, test, results, resultfile):
    baseline_file = os.path.join(testsuitedir, "tests", test, "bench.yaml")
    shutil.copyfile(baseline_file, os.path.join(outdir, test + ".expected"))
    if os.path.exists(baseline_file):
        baseline = e3.yaml.load_with_config(baseline_file, {})
    else:
        baseline = {"cvc4": 100, "altergo": 100, "z3": 100}
    res = True
    with open(os.path.join(outdir, test + ".diff"), "w") as diff_fn:
        for prover in all_provers:
            res = res and compare_baseline(
                baseline[prover], results[prover], prover, diff_fn
            )
    if res:
        resultfile.write(test + ":OK\n")
    else:
        resultfile.write(test + ":DIFF\n")


def compute_results(resultdir, outdir, testsuitedir, resultfile):
    dirs = os.listdir(resultdir)
    for test in dirs:
        mydir = os.path.join(resultdir, test)
        if not os.path.isdir(mydir):
            continue
        results = {}
        with open(os.path.join(outdir, test + ".out"), "w") as f:
            for p in all_provers:
                results[p] = compute_stat_count(os.path.join(mydir, p + ".json"))
                f.write(p + ":")
                f.write(str(results[p]))
                f.write("\n")
        compute_test_status(testsuitedir, outdir, test, results, resultfile)


def produce_version_output(outdir, resultfile):
    resultfile.write("version:XFAIL:always fails\n")
    with open(os.path.join(outdir, "version.out"), "w") as f:
        for p in all_provers:
            exec_name = "alt-ergo" if p == "altergo" else p
            f.write(subprocess.check_output([exec_name, "--version"]).decode("utf-8"))


def main():
    args = parse_arguments()
    if os.path.exists(args.outdir):
        shutil.rmtree(args.outdir)
    os.mkdir(args.outdir)
    results_file = os.path.join(args.outdir, "results")
    with open(results_file, "w") as f:
        produce_version_output(args.outdir, f)
        compute_results(args.resultsdir, args.outdir, args.testsuite_dir, f)


if __name__ == "__main__":
    main()
