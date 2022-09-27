from subprocess import call
import os

os.environ["SPARKLIB_OBJECT_DIR"] = "obj"

call (["gprbuild", "-q", "-P", "test.gpr"])
