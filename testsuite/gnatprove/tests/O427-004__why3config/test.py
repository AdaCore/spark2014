import subprocess
import os.path
from test_support import grep, spark_install_path

why3 = os.path.join(spark_install_path(), "libexec", "spark", "bin", "why3")
output = subprocess.check_output(
    [why3, "config", "-C", "toto.conf", "detect"], stderr=subprocess.STDOUT
)
output = output.splitlines()
output = grep(rb"Save config", output)
for line in output:
    print(line.decode("utf-8"))
