from test_support import ls, spark_install_path
import os.path

installpath = spark_install_path()

print("main bin/ dir")
ls(os.path.join(installpath, "bin"))
print("libexec/spark/bin/ dir")
ls(os.path.join(installpath, "libexec", "spark", "bin"), filter_output=".*dll")
print("libexec/spark/share dir")
ls(os.path.join(installpath, "libexec", "spark", "share"), filter_output="gcc-*")
