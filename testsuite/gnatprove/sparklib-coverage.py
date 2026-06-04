#! /usr/bin/env python

import glob
import os.path
import subprocess
import shutil
import tempfile

sparklib_project_path_env = "SPARKLIB_PROJECT_PATH"


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


def report_project(covtempdir):
    shared_project = os.path.join(
        covtempdir, "sparklib_bodymode", "lib", "gnat", "sparklib_internal.gpr"
    )
    if os.path.isfile(shared_project):
        return shared_project, "True"

    project_root = os.environ.get(sparklib_project_path_env)
    if project_root:
        source_project = os.path.join(project_root, "sparklib_internal.gpr")
        if os.path.isfile(source_project):
            return source_project, "False"

    return "../../include/sparklib_internal.gpr", "False"


def produce_report(covlibdir, covtempdir):
    shutil.rmtree(covlibdir)
    trf = tracefiles(covtempdir)
    sid = sidfiles(covtempdir)
    try:
        project_file, sparklib_installed = report_project(covtempdir)
        os.environ["SPARKLIB_INSTALLED"] = sparklib_installed
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
            project_file,
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
