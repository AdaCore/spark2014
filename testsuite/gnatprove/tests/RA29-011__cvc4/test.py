from e3.env import Env
from test_support import run_command, spark_install_path
import os.path

installdir = spark_install_path()
bindir = os.path.join(installdir, "libexec", "spark", "bin")
Env().add_path(bindir)

process = run_command(["cvc5", "--show-config"])
lines = process.out.splitlines()
# First three lines of cvc5 output contain date and exact compiler version, so
# remove this output. We also remove the "scm" line which refers to the exact
# git commit in some builds. Same for "portfolio", which is only available on
# Linux and not on Windows, but we don't use it anyway.
for line in lines[3:]:
    if not line.startswith(("scm", "portfolio")):
        print(line)
