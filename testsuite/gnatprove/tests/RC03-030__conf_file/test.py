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

totosh = os.path.join (os.getcwd(), "toto.sh")
# This should add a prover of type Z3 (which is recognized using the --version
# string (see why3/share/provers-detection-data.conf)
# "z3_42" is the shortcut and "z3" is the family of the prover.
# TODO ??? this does not work yet but will soon in Why3.
output = subprocess.check_output([why3config, "-C", "toto.conf", "--add-prover", "z3_42","z3", totosh],
                                 stderr=subprocess.STDOUT)

sys.stdout = open('result2', 'w')

with open("toto.conf", 'r') as outfile:
    for l in outfile:
        if "name" in l or "version" in l:
            print l

# Here we check that something was added to the why3config. We cannot use the
# whole why3config because there are a lot of platform dependant paths.
sys.stdout = sys.__stdout__
os.system("diff result1 result2")

# Here we should not have errors linked to absolute path for drivers.
# Typically: "Could not find driver file alt_ergo referenced from toto.conf".
prove_all(opt=["--why3-conf=toto.conf", "-f", "--prover=z3_42"], cache_allowed=False)

os.remove (totosh)

# Here we should have an error because totosh is inside toto.conf but the
# file/executable does not exist.
prove_all(opt=["--why3-conf=toto.conf", "-f", "--prover=z3_42"], cache_allowed=False)
