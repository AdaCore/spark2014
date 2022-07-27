from test_support import prove_all, TESTDIR
import os
import sys

# This test aims at proving the correctness of Fold when bodies are hidden.
# Everything should be proved but the axioms in the three Fold theories
# (7 unproved checks in SPARK.Higher_Order.Fold.ads)

contains_manual_proof = False


def replay():
    os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR
    prove_all(
        procs=16,
        level=3,
        opt=[
            "-u",
            "test_higher_order.ads",
            "-u",
            "test_higher_order1.ads",
            "-u",
            "test_higher_order2.ads",
            "-u",
            "test_higher_order3.ads",
        ],
    )


if __name__ == "__main__":
    sys.stdout = open("result", "w")

    os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR
    prove_all(
        steps=0,
        replay=True,
        opt=[
            "-u",
            "test_higher_order.ads",
            "-u",
            "test_higher_order1.ads",
            "-u",
            "test_higher_order2.ads",
            "-u",
            "test_higher_order3.ads",
        ],
    )

    sys.stdout = sys.__stdout__

    count = 0

    f = open("result", "r")
    for line in f:
        if "medium" in line:
            count += 1
        print(line)

    if not (count == 15):
        print("FAILED There should be exactly 15 axioms in this tests")
