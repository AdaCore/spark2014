from test_support import *
import subprocess
import os.path

why3config = os.path.join(spark_install_path(), "libexec", "spark", "bin", "why3config")
output = subprocess.check_output([why3config, "-C", "toto.conf", "--detect-provers"],
                                 stderr=subprocess.STDOUT)

sys.stdout = open('result1', 'w')

with open("toto.conf", 'r') as outfile:
    for l in outfile:
        if "name" in l or "version" in l:
            print l

sys.stdout = sys.__stdout__

cwd = os.getcwd()
# Add path to current folder (that contains z3-4.4.0)
os.environ["PATH"] += os.pathsep + cwd

# First compile our own Z3: we cannot use a script as we are not sure where sh
# or python is located on all machines(dev and nightly). The simplest was to
# compile it here.
# Using src/main.adb as name to avoid that prove_all tries to prove it.
output = subprocess.check_output(["gprbuild", "-P", "src/main.gpr", "src/main.adb", "-o", "../z3-4.4.0"],
                                 stderr=subprocess.STDOUT)

# To make this work, we had to take a prover accepted by
# share/provers-detection-data-conf: z3-4.4.0
fakez3 = os.path.join (cwd, "z3-4.4.0")

# This should add a prover of type Z3 (which is recognized using the -version
# string (see why3/share/provers-detection-data.conf)
# "z3_4.4.0" is the shortcut and "z3" is the family of the prover.
output = subprocess.check_output([why3config, "-C", "toto.conf", "--debug", "autodetect", "--add-prover", "z3","z3_4.4.0", fakez3],
                                 stderr=subprocess.STDOUT)

sys.stdout = open('result2', 'w')

with open("toto.conf", 'r') as outfile:
    for l in outfile:
        if "name" in l or "version" in l:
            print l

# Here we check that something was added to the why3config. We cannot use the
# whole why3config because there are a lot of platform dependant paths.
sys.stdout = sys.__stdout__
print("Simplified version of toto.conf before and after adding prover. They should differ")
# Flushing here to avoid "reordering of output print" (probably because diff
# prints to stderr.
sys.stdout.flush()
os.system("diff -q result1 result2")

# Here we should not have errors linked to absolute path for drivers.
# Typically: "Could not find driver file alt_ergo referenced from toto.conf".
prove_all(opt=["--why3-conf=toto.conf", "-f", "--prover=z3_4.4.0"], cache_allowed=False)

os.remove (fakez3)

# Here we should have an error because totosh is inside toto.conf but the
# file/executable does not exist.
prove_all(opt=["--why3-conf=toto.conf", "-f", "--prover=z3_4.4.0"], cache_allowed=False)
