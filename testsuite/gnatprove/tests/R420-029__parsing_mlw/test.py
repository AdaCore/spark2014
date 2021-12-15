from e3.env import Env
from e3.os.process import Run
from test_support import spark_install_path
import os.path


installdir = spark_install_path()
bindir = os.path.join(installdir, "libexec", "spark", "bin")
Env().add_path(bindir)

process = Run(["gnatwhy3", "--debug", "incorrect.mlw"])
print(process.out)
