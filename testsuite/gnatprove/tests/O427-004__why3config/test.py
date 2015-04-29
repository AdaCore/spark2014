from subprocess import call
from test_support import spark_install_path
import os.path

why3config = os.path.join(spark_install_path(), "libexec", "spark", "bin", "why3config")
call([why3config, "-C", "toto.conf", "--detect-provers"])
