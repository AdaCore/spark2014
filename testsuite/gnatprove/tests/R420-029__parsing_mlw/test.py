from e3.env import Env
from test_support import *


installdir = spark_install_path()
bindir = os.path.join(installdir, 'libexec', 'spark', 'bin')
Env().add_path(bindir)

process = Run(["gnatwhy3", "--debug", "incorrect.mlw"])
print(process.out)
