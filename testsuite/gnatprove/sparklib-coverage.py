#! /usr/bin/env python

import glob
import os.path
import subprocess
import shutil
import sys
import tempfile

sys.path.append(os.path.join(os.path.dirname(__file__), "lib", "python"))

import test_support  # noqa: E402


def run_command(args):
    subprocess.run(args, check=True)


def setup_coverage():
    tmpdir = tempfile.mkdtemp(prefix="sparkcov")
    run_command(["gnatcov", "setup", f"--prefix={tmpdir}"])
    project_path = os.path.join(tmpdir, "share", "gpr")
    os.environ["GPR_PROJECT_PATH"] = (
        os.environ.get("GPR_PROJECT_PATH", "") + f":{project_path}"
    ).lstrip(":")
    return tmpdir


def run_testsuite(tempdir):
    subprocess.run(
        [
            "./run-tests",
            "--testlist=sparklib/coverage.manifest",
            "--coverage",
            "--disc=large",
            "-d",
            tempdir,
        ]
    )


def tracefiles(covtempdir):
    tracefiles = tempfile.NamedTemporaryFile(delete=False)
    files = glob.glob(os.path.join(f"{covtempdir}/**", "*.srctrace"), recursive=True)
    for file in files:
        tracefiles.write(file.encode("utf-8") + b"\n")
    tracefiles.close()
    return tracefiles


def sidfiles(covtempdir):
    files = glob.glob(os.path.join(f"{covtempdir}/**", "*.sid"), recursive=True)
    if len(files) > 0:
        sidfiles = tempfile.NamedTemporaryFile(delete=False)
        for file in files:
            sidfiles.write(file.encode("utf-8") + b"\n")
        sidfiles.close()
        return sidfiles
    print("didn't find any sid files")
    exit(1)


def report_project():
    """Return the SPARKlib project the coverage report is computed against.

    It is the very project the instrumented tests were built against, so the
    report covers the same sources.
    """
    project_dir, _ = test_support.resolve_sparklib_location()
    return os.path.join(project_dir, "sparklib_internal.gpr")


def produce_report(covlibdir, covtempdir):
    shutil.rmtree(covlibdir)
    trf = tracefiles(covtempdir)
    sid = sidfiles(covtempdir)
    try:
        args = [
            "gnatcov",
            "coverage",
            "--annotate=dhtml",
            "--level=stmt",
            "--externally-built-projects",
            "--output-dir=sparklib-report",
            "--sid",
            f"@{sid.name}",
            "-P",
            report_project(),
            # The instrumented tests are built in body mode, so the report has
            # to be computed against the same variants of the library units.
            f"-X{test_support.sparklib_body_mode_var}=On",
            f"@{trf.name}",
        ]
        run_command(args)
        print("Find the coverage report in sparklib-report/html")
    finally:
        os.unlink(trf.name)
        os.unlink(sid.name)


def main():
    covlibdir = setup_coverage()
    covtempdir = "covtemp"
    try:
        os.rmdir(covtempdir)
    except OSError:
        pass
    run_testsuite(covtempdir)
    produce_report(covlibdir, covtempdir)


if __name__ == "__main__":
    main()
