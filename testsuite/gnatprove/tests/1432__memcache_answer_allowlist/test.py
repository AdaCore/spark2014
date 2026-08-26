import os
import shutil
import subprocess

from test_support import gprbuild, spark_install_path

# Check which prover runs the memcached wrapper is willing to cache. Only a run
# that concluded something is cached: output holding a recognized prover answer.
# Output of a run that hit the memory limit, was killed, or failed the way gappa
# does is not cached, so that it is not replayed forever. A killed prover that
# printed nothing must in addition leave the cache directory clean.

CACHE = os.path.abspath("cache")
FAKE_PROVER_DIR = os.path.abspath(os.path.join("fake", "obj"))

PRIVATE_BIN = os.path.join(spark_install_path(), "libexec", "spark", "bin")

# Build the fake prover. The wrapper is not on the PATH of a packaged install,
# where it lives in the private bin dir, so add that dir at the end of the PATH.
# The fake prover goes at the front, so that it shadows the real prover shipped
# in that same private bin dir.

gprbuild(opt=["-P", os.path.join("fake", "fake.gpr")])
os.environ["PATH"] = (
    FAKE_PROVER_DIR + os.pathsep + os.environ["PATH"] + os.pathsep + PRIVATE_BIN
)

# The wrapper hashes its last argument as a file, so that file must exist

with open("vc.mlw", "w", encoding="utf-8") as vc_file:
    vc_file.write("dummy\n")


def check(answer, expected):
    """Run the wrapper on the fake prover and report what reached the cache"""
    shutil.rmtree(CACHE, ignore_errors=True)
    os.makedirs(CACHE)
    os.environ["FAKE_ANSWER"] = answer
    subprocess.run(
        ["spark_memcached_wrapper", "salt", f"file:{CACHE}", "cvc5", "vc.mlw"],
        stdout=subprocess.DEVNULL,
    )
    entries = len(os.listdir(CACHE))
    if entries == expected:
        print(f"OK: {answer}")
    else:
        print(f"{answer}: expected {expected} cache entries but found {entries}")


check("unsat", 1)
check("alt_ergo", 1)
check("steps", 1)
check("memory", 0)
check("gappa", 0)
check("killed", 0)
