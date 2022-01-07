import os.path
from test_support import prove_all, spark_install_path
from subprocess import call

prove_all(cache_allowed=False)

installdir = spark_install_path()
why3 = os.path.join(installdir, "libexec", "spark", "bin", "why3")
call([why3, "session", "info", "--stats", os.path.join("gnatprove", "add__addtwo")])
