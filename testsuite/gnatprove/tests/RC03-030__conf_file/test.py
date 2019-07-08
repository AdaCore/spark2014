from test_support import *
import subprocess
import os.path

why3config = os.path.join(spark_install_path(), "libexec", "spark", "bin", "why3config")

sys.stdout = open('result1', 'w')

with open("toto.conf", 'r') as outfile:
    for l in outfile:
        if "name" in l or "version" in l:
            print l

sys.stdout = sys.__stdout__

cwd = os.getcwd()
# Add path to current folder (that contains cvc3-2.4.1)
os.environ["PATH"] += os.pathsep + cwd
path_save = os.environ["PATH"]

# First compile our own cvc3: we cannot use a script as we are not sure where sh
# or python is located on all machines(dev and nightly). The simplest was to
# compile it here.
# Using src/main.adb as name to avoid that prove_all tries to prove it.
output = subprocess.check_output(["gprbuild", "-P", "src/main.gpr", "src/main.adb", "-o", "../cvc3-2.4.1"],
                                 stderr=subprocess.STDOUT)

# To make this work, we had to take a prover accepted by
# share/provers-detection-data-conf: cvc3-2.4.1
fakecvc3 = os.path.join (cwd, "cvc3-2.4.1")

# hide all other provers from the path
os.environ["PATH"] = cwd

# This should add a prover of type cvc3 (which is recognized using the -version
# string (see why3/share/provers-detection-data.conf)
# "cvc3_2.4.1" is the shortcut and "cvc3" is the family of the prover.
output = subprocess.check_output([why3config, "-C", "toto.conf", "--debug", "autodetect", "--add-prover", "cvc3","cvc3_2.4.1", fakecvc3],
                                 stderr=subprocess.STDOUT)

os.environ["PATH"] = path_save

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
prove_all(opt=["--why3-conf=toto.conf", "-f", "--prover=cvc3"], cache_allowed=False)

os.remove (fakecvc3)

# Here we should have an error because totosh is inside toto.conf but the
# file/executable does not exist.
prove_all(opt=["--why3-conf=toto.conf", "-f", "--prover=cvc3"], cache_allowed=False)
