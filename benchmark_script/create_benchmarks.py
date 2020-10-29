#!/usr/bin/env python

import os
import shutil
import subprocess

def create_benchmarks(datadir, limit):
    os.mkdir(datadir)
    olddir = os.getcwd()
    try:
        os.chdir("../testsuite/gnatprove")
        p = subprocess.run(["./run-tests", "--benchmarks",
                            "--temp-dir=" + datadir, "--disable-cleanup"] + limit)
        if os.path.exists("internal"):
            print("warning: collected VCs include internal tests")
    finally:
        os.chdir(olddir)

def collate_benchmarks(datadir, benchdir):
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

                test_name = path.split("/")[2]
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

def create_collated_benchs(benchdir="bench", limit=[]):
    datadir = os.path.join("/tmp", "sparkbench")
    if os.path.exists(datadir):
        shutil.rmtree(datadir)
    if os.path.exists(benchdir):
        shutil.rmtree(benchdir)
    create_benchmarks(datadir, limit)
    collate_benchmarks(datadir, benchdir)

def main():
    create_collated_benchs()

if __name__ == "__main__":
    # execute only if run as a script
    main()
