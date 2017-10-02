from test_support import *
import time

""" This tests is a commandline test for the itp server. It launches a server as
a background process, and then pass it request in JSON. The output to be checked
are notifications written in JSON"""

# This launches the itp_server
def launch_server(limit_line="", input_file=""):

    installdir = spark_install_path()
    bindir = os.path.join(installdir, 'libexec', 'spark', 'bin')
    Env().add_path(bindir)

    cmd = ["gnat_server"]
    cmd += ["--limit-line"]
    cmd += [limit_line]
    cmd += ["test.mlw"]
    # Create a pipe to give request to the process one by one. TODO check that
    # this works like this in python.
    read, write = os.pipe()
    process = Run (cmd, cwd="gnatprove", input=read, bg=True, timeout=30)
    with open ("test.in", "r") as in_file:
        for l in in_file:
            sleep(3)
            print(l)
            os.write(write, l)
    process.wait()
    s = process.out
    return s

prove_all(counterexample=False, prover=["cvc4"])
sleep(5)
result = launch_server(limit_line="test.adb:11:16:VC_POSTCONDITION", input_file="test.in")
print(result)
