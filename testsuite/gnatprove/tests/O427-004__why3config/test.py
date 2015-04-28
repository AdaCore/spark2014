from subprocess import call
from distutils.spawn import find_executable
import os.path

gnatprove_path = find_executable("gnatprove")
spark_prefix = os.path.dirname(os.path.dirname(gnatprove_path))
why3config = os.path.join(spark_prefix, "libexec", "spark", "bin", "why3config")
call([why3config, "-C", "toto.conf", "--detect-provers"])
