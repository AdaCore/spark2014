#!/usr/bin/env python

from config import TIMES, STEPS, STEP_FLAGS

from glob import glob
import os
import re
import sys
import random

baseline = [
    "--rewrite-step=0",
    "--bitblast-step=0",
    "--cnf-step=0",
    "--parse-step=0",
    "--preprocess-step=0",
    "--decision-step=0",

    "--bv-sat-conflict-step=5",

    "--theory-check-step=10",
    "--quantifier-step=10",
    "--restart-step=10",
    "--sat-conflict-step=10",
    "--lemma-step=10",

    "--no-cbqi",
]

oldflags = baseline + ["--no-cond-rewrite-quant"]

newflags = [
    "--rewrite-step=0",
    "--preprocess-step=0",
    "--parse-step=0",

    "--decision-step=1",
    "--bv-sat-conflict-step=1",
    "--sat-conflict-step=1",
    "--quantifier-step=1",
    "--theory-check-step=1",

    "--lemma-step=10",
    "--cnf-step=10",
    "--bitblast-step=10",
    "--restart-step=10",

    "--no-cbqi",
    "--no-cond-rewrite-quant",
    "--boolean-term-conversion-mode=native",
]

step_add = 10000
step_mul = 25

random.seed(123456)

def file_selector(fn):
    return random.randint(0, 100) < 6
    #return re.match("0[0-5].*", fn) is not None

ALL_SMT = filter(file_selector, map(os.path.basename, glob("cvc4/*.smt2")))

cvc4_bin = "cvc4"
options  = newflags

if len(sys.argv) == 1:
    new_dir = None
elif len(sys.argv) == 2:
    new_dir = sys.argv[1]
    if new_dir == "baseline":
        cvc4_bin = "./cvc4_baseline"
        options = baseline
    elif new_dir == "oldflags":
        options = oldflags
else:
    print "usage make_stats.py [dir]"
    sys.exit(1)

os.system("rm -rf res_* tim_* spec_*")

def produce_stats():
    DIRS = ["res_%u" % x for x in sorted(STEPS, reverse=True)] + \
           ["tim_%u" % x for x in sorted(TIMES, reverse=True)]

    ALL_TGT = [os.path.join(dn, f.replace(".smt2", ".res"))
               for dn in DIRS
               for f in ALL_SMT]

    with open("Makefile", "w") as fd:
        fd.write("TGT:=%s\n" % " ".join(ALL_TGT))
        fd.write("\n")

        fd.write("all: ${TGT}\n")
        fd.write("\n")

        for t in STEPS:
            fd.write("res_%u:\n" % t)
            fd.write("\tmkdir res_%u\n" % t)
            fd.write("\n")

        for t in TIMES:
            fd.write("tim_%u:\n" % t)
            fd.write("\tmkdir tim_%u\n" % t)
            fd.write("\n")

        for t in STEPS:
            fd.write("res_%u/%%.res: cvc4/%%.smt2 res_%u\n" % (t, t))
            fd.write("\t@%s " % cvc4_bin)
            fd.write("--stats ")
            fd.write("--rlimit=%u " % (step_add + step_mul * t))
            fd.write(" ".join(options))
            fd.write(" $< 2>&1 | ")
            fd.write("egrep 'sat/unsat|resourceUnitsUsed|totalTime'")
            fd.write(" > $@\n")
            fd.write("\t@echo done: $@\n")
            fd.write("\n")

        for t in TIMES:
            fd.write("tim_%u/%%.res: cvc4/%%.smt2 tim_%u\n" % (t, t))
            fd.write("\t@%s " % cvc4_bin)
            fd.write("--stats ")
            fd.write("--tlimit=%u " % t)
            fd.write(" ".join(options))
            fd.write(" $< 2>&1 | ")
            fd.write("egrep 'sat/unsat|resourceUnitsUsed|totalTime'")
            fd.write(" > $@\n")
            fd.write("\t@echo done: $@\n")
            fd.write("\n")

    print "%u VCs" % len(ALL_SMT)
    print "using %s" % cvc4_bin
    print "options:"
    for o in sorted(options):
        print "\t%s" % o

def produce_spectrum():

    maxlen = max(map(len, STEP_FLAGS))

    DIRS = ["spec_%s" % x for x in STEP_FLAGS]

    ALL_TGT = [os.path.join(dn, f.replace(".smt2", ".res"))
               for f in ALL_SMT
               for dn in DIRS]

    with open("Makefile", "w") as fd:
        fd.write("TGT:=%s\n" % " ".join(ALL_TGT))
        fd.write("\n")

        fd.write("all: ${TGT}\n")
        fd.write("\n")

        for d in DIRS:
            fd.write("%s:\n" % d)
            fd.write("\tmkdir %s\n" % d)
            fd.write("\n")

        for i, flag in enumerate(STEP_FLAGS):
            fd.write("spec_%s/%%.res: cvc4/%%.smt2 spec_%s\n" % (flag, flag))
            fd.write("\t@%s " % cvc4_bin)
            fd.write("--stats ")
            fd.write("--tlimit=10000 --hard-limit --cpu-time ")
            fd.write("--%s-step=1 " % flag)
            for other_flag in STEP_FLAGS[:i] + STEP_FLAGS[i+1:]:
                fd.write("--%s-step=0 " % other_flag)
            fd.write("--no-cbqi ")
            fd.write("--no-cond-rewrite-quant ")
            # fd.write("--boolean-term-conversion-mode=native ")
            fd.write(" $< 2>&1 | ")
            fd.write("egrep 'sat/unsat|resourceUnitsUsed|totalTime'")
            fd.write(" > $@\n")
            fd.write("\t@echo '[%*s]' $@\n" % (maxlen, flag))
            fd.write("\n")

produce_stats()

os.system("make -j16")
if new_dir is not None:
    os.system("rm -rf %s" % new_dir)
    os.system("mkdir %s" % new_dir)
    os.system("mv res_* tim_* spec_* %s/" % new_dir)
