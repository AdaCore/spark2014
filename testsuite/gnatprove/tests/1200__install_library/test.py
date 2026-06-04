import os

from test_support import prove_all, gprbuild, run_command, grep

installdir = os.path.join(os.getcwd(), "install")
installed_gpr = os.path.join(installdir, "share", "gpr", "counter_lib.gpr")
installed_ali = os.path.join(
    installdir, "lib", "counter_lib", "gnatprove", "counter.ali"
)

# Prove the library project. It contains subprograms that touch global
# variables and require proof, and it relies on global generation rather than
# on explicit Global contracts.
print("=== Proving library ===")
prove_all(project="counter_lib.gpr")

# Build and install the library with gprinstall. The summary ALI files
# produced by GNATprove are copied automatically into the installation.
gprbuild(["-P", "counter_lib.gpr"])
run_command(
    ["gprinstall2", "-P", "counter_lib.gpr", "--prefix=" + installdir, "-p", "-f"]
)

# The installed project must be externally built.
with open(installed_gpr) as f:
    installed_lines = f.read().splitlines()
if grep(r'\s*for Externally_Built use "True"', installed_lines):
    print("PASS: installed project is externally built")
else:
    print("FAIL: installed project is not externally built")

# The summary ALI files must be installed in the gnatprove subfolder of the
# installed library's ALI directory.
if os.path.isfile(installed_ali):
    print("PASS: summary ALI files installed in gnatprove subfolder")
else:
    print("FAIL: summary ALI files missing from gnatprove subfolder")

# Prove the main project against the installed (externally built) library. The
# main project depends on the library only through its installation, found via
# GPR_PROJECT_PATH; it is proved from its own directory so that the library
# sources cannot be picked up directly. Because the installed summary ALI files
# record the global effects of the library subprograms, GNATprove does not
# assume that the library's hidden state is unchanged across a call: the
# assertion in Run is reported as possibly failing, and no "assumed-global"
# warning is emitted.
print("=== Proving main ===")
os.environ["GPR_PROJECT_PATH"] = (
    os.path.join(installdir, "share", "gpr")
    + os.pathsep
    + os.environ.get("GPR_PROJECT_PATH", "")
)
prove_all(project="main.gpr", cwd="app")
