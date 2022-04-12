#!/usr/bin/env python

import argparse
import os
import re
import shutil
import subprocess
import config

descr = """
Create VC files for selected tests from the testsuite. Store the VCs in the
target folder, using subfolders for tests and provers.
"""

testname_regex = re.compile("tmp[^/]*\/([^/]*)\/src")  # noqa


def extract_testname(path):
    g = testname_regex.search(path)
    assert g is not None
    return g.group(1)


def create_if_needed(p):
    if not os.path.exists(p):
        os.mkdir(p)


def copy_vcs(tmpdir, resultdir, prover):
    create_if_needed(resultdir)
    for path, _dirs, files in os.walk(tmpdir):
        for f in files:
            if f.endswith(".smt2") or f.endswith(".ae"):
                testname = extract_testname(path)
                create_if_needed(os.path.join(resultdir, testname))
                create_if_needed(os.path.join(resultdir, testname, prover))
                src = os.path.join(path, f)
                dest = os.path.join(resultdir, testname, prover, f)
                shutil.copyfile(src, dest)


def create_benchmarks(testsuitedir, tmpdir, resultdir, testlist):
    """Call the testsuite with the --benchmark switch for all provers. This
    switch runs the testsuite in benchmark mode, which forces the use of the
    given prover, and also substitutes the prover for the prover with "fake_"
    prefix. The "fake" prover proves all goals, so that gnatprove generates all
    goals for this prover.  Due to how "run-tests" works, running the testsuite
    creates separate build spaces, so all runs start from scratch.
    Arguments:
        testsuitedir: path to the testsuite
        tmpdir:       used to store temp files for the testsuite; contains the VCs
                      temporarily
        resultdir:    place to store the VCs
        testlist:     Manifest file to select tests
    """

    driver = os.path.join(testsuitedir, "run-tests")
    for prover in config.all_provers:
        if os.path.exists(tmpdir):
            shutil.rmtree(tmpdir)
        os.mkdir(tmpdir)
        if testlist is None:
            testlistargs = []
        else:
            testlistargs = ["--testlist=" + testlist]
        subprocess.run(
            [
                driver,
                "--benchmark=" + prover,
                "--disc=large",
                "--temp-dir=" + tmpdir,
                "--disable-cleanup",
            ]
            + testlistargs
        )
        copy_vcs(tmpdir, resultdir, prover)
    if os.path.exists(os.path.join(testsuitedir, "internal")):
        print("warning: collected VCs include internal tests")


def create_collated_benchs(testsuitedir, benchdir, testlist):
    datadir = os.path.join(benchdir, "tmp")
    resultdir = os.path.join(benchdir, "bench")
    create_if_needed(benchdir)
    if os.path.exists(datadir):
        shutil.rmtree(datadir)
    if os.path.exists(resultdir):
        shutil.rmtree(resultdir)
    create_benchmarks(testsuitedir, datadir, resultdir, testlist)


def parse_arguments():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument(
        "--testsuite-dir",
        type=str,
        required=True,
        help="directory which contains the testsuite",
    )
    parser.add_argument(
        "--target-dir", type=str, required=True, help="directory to store VCs in"
    )
    parser.add_argument(
        "--testlist",
        type=str,
        default=None,
        help="file that contains list of tests to generate VCs for",
    )
    args = parser.parse_args()
    return args


def main():
    args = parse_arguments()
    create_collated_benchs(
        testsuitedir=args.testsuite_dir,
        benchdir=args.target_dir,
        testlist=args.testlist,
    )


if __name__ == "__main__":
    # execute only if run as a script
    main()
