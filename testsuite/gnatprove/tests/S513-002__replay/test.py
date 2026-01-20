from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

prove_all(
    opt=["--level=4", "--function-sandboxing=off", "--counterexamples=off"],
    sparklib=True,
    cache_allowed=False,
)
print("--------------------------------------")
prove_all(
    opt=["--function-sandboxing=off", "--counterexamples=off"],
    replay=True,
    sparklib=True,
    cache_allowed=False,
)
