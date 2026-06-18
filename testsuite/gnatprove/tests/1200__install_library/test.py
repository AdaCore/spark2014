import os

from test_support import prove_all, gprbuild, run_command, grep

# Base GPR_PROJECT_PATH, restored for each variant so that only the library
# installed by that variant is visible to the main project.
base_gpr_path = os.environ.get("GPR_PROJECT_PATH", "")


def check_variant(variant_dir, gprinstall_tool):
    """Install a library variant and prove a depending main project.

    The library is proved (it relies on global generation rather than explicit
    Global contracts), built, and installed with the given gprinstall tool. The
    test then checks that the installed project is externally built and that the
    summary ALI files produced by GNATprove end up in the gnatprove subfolder of
    the installed library's ALI directory. Finally the main project is proved
    against the installed (externally built) library: because the summary ALI
    files record the global effects of the library subprograms, GNATprove does
    not assume that the library's hidden state is unchanged across a call, so the
    assertion in Run is reported as possibly failing and no "assumed-global"
    warning is emitted.
    """
    print(f"=== Variant {variant_dir} installed with {gprinstall_tool} ===")
    project = os.path.join(variant_dir, "counter_lib.gpr")
    installdir = os.path.join(os.getcwd(), variant_dir, "install")

    # Prove, build and install the library.
    prove_all(project=project)
    gprbuild(["-P", project])
    run_command([gprinstall_tool, "-P", project, "--prefix=" + installdir, "-p", "-f"])

    # The installed project must be externally built.
    installed_gpr = os.path.join(installdir, "share", "gpr", "counter_lib.gpr")
    with open(installed_gpr) as f:
        installed_lines = f.read().splitlines()
    if grep(r'\s*for Externally_Built use "True"', installed_lines):
        print("PASS: installed project is externally built")
    else:
        print("FAIL: installed project is not externally built")

    # The summary ALI files must be installed in the gnatprove subfolder of the
    # installed library's ALI directory.
    installed_ali = os.path.join(
        installdir, "lib", "counter_lib", "gnatprove", "counter.ali"
    )
    if os.path.isfile(installed_ali):
        print("PASS: summary ALI files installed in gnatprove subfolder")
    else:
        print("FAIL: summary ALI files missing from gnatprove subfolder")

    # Prove the main project against this installed library only. The main
    # project is proved from its own directory so that the library sources
    # cannot be picked up directly.
    os.environ["GPR_PROJECT_PATH"] = (
        os.path.join(installdir, "share", "gpr") + os.pathsep + base_gpr_path
    )
    prove_all(project="main.gpr", cwd="app")


# The legacy gprinstall does not install the summary files on its own, so the
# library project carries an explicit Install package. The newer gprinstall2
# installs them automatically, with no extra configuration in the project file.
check_variant("variant_artifacts", "gprinstall")
check_variant("variant_native", "gprinstall2")
