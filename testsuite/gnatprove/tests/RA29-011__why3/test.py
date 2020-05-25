from e3.env import Env
from test_support import Run, spark_install_path
import os.path

installdir = spark_install_path()
bindir = os.path.join(installdir, 'libexec', 'spark', 'bin')
Env().add_path(bindir)
process = Run(["gnatwhy3", "--show-config"])
print(process.out)
