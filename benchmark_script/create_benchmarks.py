#!/usr/bin/env python

import os
import shutil
import subprocess
import sys

def create_benchmarks(testsuitedir, datadir, extra_args):
    """ Call the testsuite with the --benchmark switch for all provers. This
    switch runs the testsuite in benchmark mode, which forces the use of the
    given prover, and also substitutes the prover for the prover with "fake_"
    prefix. The "fake" prover proves all goals, so that gnatprove generates all
    goals for this prover.  Due to how "run-tests" works, running the testsuite
    creates separate build spaces, so all runs start from scratch.
    Arguments:
        testsuitedir: path to the testsuite
        datadir:      path to store VC files
        extra_args:   extra arguments passed to testsuite, can be used to reduce
                      the number of tests by passing a filter
    """

    os.mkdir(datadir)
    olddir = os.getcwd()
    try:
        os.chdir(testsuitedir)
        p = subprocess.run(["./run-tests", "--benchmark=cvc4",
                            "--temp-dir=" + datadir, "--disable-cleanup"] + extra_args)
        p = subprocess.run(["./run-tests", "--benchmark=altergo",
                            "--temp-dir=" + datadir, "--disable-cleanup"] + extra_args)
        p = subprocess.run(["./run-tests", "--benchmark=z3",
                            "--temp-dir=" + datadir, "--disable-cleanup"] + extra_args)
        if os.path.exists("internal"):
            print("warning: collected VCs include internal tests")
    finally:
        os.chdir(olddir)

def collate_benchmarks(datadir, benchdir):
    """Copy all VCs from the temp dirs inside [datadir] of the testsuite into
    folders for each prover."""
    bm = {}

    smt2_driver_prefix = ";; produced by "

    for path, dirs, files in os.walk(datadir):
        for f in files:
            if f.endswith(".smt2") or f.endswith(".why"):
                # Strip extension and trailing numbers added by why3
                tmp = f.rsplit(".", 1)[0]
                vc_name = tmp.rstrip("0123456789")
                vc_index = tmp[len(vc_name):]
                if vc_index == "":
                    vc_index = 1
                else:
                    vc_index = int(vc_index)

                test_name = path.split("/")[4]
                name = test_name + "__" + vc_name
                name = name.replace(" ", "_")

                if f.endswith(".smt2"):
                    prover = None
                    with open(os.path.join(path, f)) as fd:
                        for raw_line in fd:
                            if raw_line.startswith(smt2_driver_prefix):
                                prover = raw_line[len(smt2_driver_prefix):]
                                prover = prover.split()[0].rsplit(".", 1)[0]
                                break
                    assert prover is not None
                else:
                    prover = "altergo"

                if name not in bm:
                    bm[name] = {prover: [os.path.join(path, f)]}
                elif prover not in bm[name]:
                    bm[name][prover] = [os.path.join(path, f)]
                else:
                    bm[name][prover].append(os.path.join(path, f))

    PROVERS = set()
    for name in bm:
        PROVERS |= set(bm[name])

    PROVERS = sorted(PROVERS)

    EXT = {
        "altergo": "why",
        "cvc4_16": "smt2",
        "z3_gnatprove": "smt2",
        "z3_gnatprove_ce":  "smt2",
        "colibri":  "smt2",
    }

    for p in PROVERS:
        os.makedirs(os.path.join(benchdir, p))

    for test in bm:
        for p in PROVERS:
            if p in bm[test]:
                for id, the_test in enumerate(sorted(bm[test][p])):
                    dst = os.path.join(benchdir,
                                       p,
                                       test + ("__%02u" % id) + "." + EXT[p])
                    assert (not os.path.exists(dst))
                    shutil.copyfile(the_test, dst)

def create_collated_benchs(testsuitedir="../testsuite/gnatprove",
                           benchdir="bench",
                           extra_args=[]):
    datadir = os.path.join("/tmp", "sparkbench")
    if os.path.exists(datadir):
        shutil.rmtree(datadir)
    if os.path.exists(benchdir):
        shutil.rmtree(benchdir)
    create_benchmarks(testsuitedir, datadir, extra_args)
    collate_benchmarks(datadir, benchdir)

def main():
    if len(sys.argv) < 3:
        print("usage: create_benchmarks.py <testsuitedir> <targetdir>")
    testsuitedir = sys.argv[1]
    targetdir = sys.argv[2]
    create_collated_benchs(testsuitedir=testsuitedir,
                           benchdir=targetdir)

if __name__ == "__main__":
    # execute only if run as a script
    main()
