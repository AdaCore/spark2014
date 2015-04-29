from test_support import *
from time import sleep
import glob

installdir = spark_install_path()
driverdir = os.path.join(installdir, 'share', 'why3', 'drivers')
driverfile = os.path.join(driverdir, 'coq.drv')
conf_file = "test.whyconf"

conf_content = """[main]
magic = 14

[prover]
command = "coqtop -batch -R %%o/why3_libs/coq_tactic Why3 -R %%o/why3_libs/coq Why3 -l %%f"
driver = "%s"
in_place = false
interactive = true
name = "Coq"
shortcut = "coq"
version = "8.4pl6"
""" % driverfile

proof = """admit.

Qed.
"""

def write_config_file():
    # create why3 configuration file
    with open(conf_file, "w") as file:
        file.write(conf_content)

def touch(fname, times=None):
    with open(fname, 'a'):
        os.utime(fname, times)

def edit_proof():
    proof_file = glob.glob("proof/Coq/greatest_common_divisor/*.v")[0]
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)


write_config_file()
prove_all()
print "======================================="
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=greatest_common_divisor.adb:10"])
print "======================================="
edit_proof()
# workaround for caching problem
touch("greatest_common_divisor.adb")
sleep(2)
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=greatest_common_divisor.adb:10"])
print "======================================="
prove_all()
