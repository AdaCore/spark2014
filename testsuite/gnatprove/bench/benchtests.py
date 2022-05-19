#!/usr/bin/env python

import argparse
import multiprocessing
import os.path
import subprocess

timelimit = 10

descr = """
   This script expects a directory structure as follows. The "benchdir"
   contains a number of folders which we call "tests". Each test folder
   contains subdirs for each prover, e.g. cvc5, z3 etc. Each such prover folder
   contains *.smt2 files.
   This script runs the corresponding prover on all smt files, storing the
   results in JSON files of the form
     benchdir/testdir/<provername>.json
"""


def parse_arguments():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument("benchdir", metavar="F", help="directory to be run on")
    parser.add_argument(
        "--testsuite-dir",
        type=str,
        default=None,
        required=True,
        help="directory which contains the testsuite",
    )
    parser.add_argument(
        "-j",
        dest="parallel",
        type=int,
        action="store",
        default=1,
        help="number of processes to run in parallel",
    )
    args = parser.parse_args()
    if args.parallel == 0:
        args.parallel = multiprocessing.cpu_count() // 2
    return args


def compute_prover_name(proverdir):
    _, p = os.path.split(proverdir)
    if p.startswith("cvc4"):
        return "cvc4"
    if p.startswith("z3"):
        return "z3"
    if p.startswith("altergo"):
        return "altergo"
    if p.startswith("cvc5"):
        return "cvc5"
    raise ValueError


def run_prover(proverdir, resultdir, testsuitedir, socket, parallel):
    """
    Run the prover on all VCs in proverdir. Compute provername from
    proverdir. Store the result json file in resultdir. Use socket for
    communication with why3server and run up to [parallel] VCs.
    """
    prover = compute_prover_name(proverdir)
    result_file = os.path.join(resultdir, prover + ".json")
    cmd = [
        "python",
        os.path.join(testsuitedir, "bench", "prover_stats.py"),
        "--prover=" + prover,
        "-j",
        str(parallel),
        "-t",
        str(timelimit),
        "--socket=" + socket,
        "-o",
        result_file,
        proverdir,
    ]
    p = subprocess.Popen(cmd)
    return p


def run_test(args):
    """Run a test. Args contains:
    benchdir: The dir where the VCs are
    socket: socket to use for communication with why3server
    parallel: use up to X processes
    testname: the name of the test
    """
    dirs = os.listdir(args["benchdir"])
    processes = []
    for d in dirs:
        mydir = os.path.join(args["benchdir"], d)
        if os.path.isdir(mydir):
            p = run_prover(
                mydir,
                args["benchdir"],
                args["testsuitedir"],
                args["socket"],
                args["parallel"],
            )
            processes.append(p)
    for p in processes:
        p.wait()


def run_bench(benchdir, parallel, testsuitedir):
    socket = os.path.join(benchdir, "benchsock.sock")
    cmd = ["why3server", "-j", str(parallel), "--logging", "--socket", socket]
    p_why3server = subprocess.Popen(cmd)
    dirs = os.listdir(benchdir)
    args = [
        {
            "testname": d,
            "benchdir": os.path.join(benchdir, d),
            "testsuitedir": testsuitedir,
            "socket": socket,
            "parallel": parallel,
        }
        for d in dirs
        if os.path.isdir(os.path.join(benchdir, d))
    ]
    with multiprocessing.Pool(parallel) as p:
        p.map(run_test, args)
    p_why3server.kill()


def main():
    args = parse_arguments()
    run_bench(args.benchdir, args.parallel, args.testsuite_dir)


if __name__ == "__main__":
    main()
