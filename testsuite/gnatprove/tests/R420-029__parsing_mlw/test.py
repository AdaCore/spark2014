from e3.env import Env
from e3.os.process import Run
from test_support import spark_install_path
import os.path


installdir = spark_install_path()
bindir = os.path.join(installdir, "libexec", "spark", "bin")
Env().add_path(bindir)

# pass a dummy number as the entity
process = Run(["gnatwhy3", "--debug", "incorrect.mlw", "--entity=1234"])
print(process.out)
