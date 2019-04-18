from test_support import *
from gnatpython.env import putenv
import os

# This test aims at proving the correctness of Fold when bodies are hidden.
# Everything should be proved but the axioms in the three Fold theories
# (7 unproved checks in SPARK.Higher_Order.Fold.ads)


contains_manual_proof = False



def replay():
    prove_all(procs=16, steps=0, vc_timeout=20,
              prover=["cvc4","z3","altergo"],
              opt=["-u", "test_higher_order.ads",
                   "-u", "test_higher_order1.ads",
                   "-u", "test_higher_order2.ads",
                   "-u", "test_higher_order3.ads"])

sys.stdout = open('result', 'w')

putenv("SPARK_LEMMAS_OBJECT_DIR", TESTDIR)
prove_all(steps=0, replay=True, opt=["-u", "test_higher_order.ads",
                                     "-u", "test_higher_order1.ads",
                                     "-u", "test_higher_order2.ads",
                                     "-u", "test_higher_order3.ads"])

sys.stdout = sys.__stdout__

count = 0

f = open('result', 'r')
for l in f:
    if "medium" in l:
        count += 1
    print l

if not (count == 9):
    print "FAILED There should be exactly 9 axioms in this tests"
