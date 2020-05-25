import subprocess
from test_support import *
import os.path

why3config = os.path.join(spark_install_path(), "libexec", "spark", "bin", "why3config")
output = subprocess.check_output([why3config, "-C", "toto.conf", "--detect-provers"],
                                 stderr=subprocess.STDOUT)
output = output.splitlines()
output = grep(rb"Save config", output)
for l in output:
    print(l.decode("utf-8"))
