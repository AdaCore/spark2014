from test_support import prove_all
import os

# Set MODE environment variable so that thumper.gpr project file is set for
# analysis instead of compilation.
os.environ["MODE"] = "Analyze"
# Set GPR_PROJECT_PATH so that dummy project files are found for GTKAda and
# AUnit.
os.environ["GPR_PROJECT_PATH"] = "dummy_projects"
prove_all(opt=["-U", "-P", "thumper/src/thumper.gpr"])
