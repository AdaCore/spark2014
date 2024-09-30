#! /usr/bin/env python

import glob
import os.path
import subprocess
import shutil
import tempfile


def setup_coverage():
    tmpdir = tempfile.mkdtemp(prefix="sparkcov")
    subprocess.run(["gnatcov", "setup", f"--prefix={tmpdir}"])
    project_path = os.path.join(tmpdir, "share", "gpr")
    os.environ["GPR_PROJECT_PATH"] = os.environ["GPR_PROJECT_PATH"] + f":{project_path}"
    return tmpdir


def run_testsuite(tempdir):
    subprocess.run(
        [
            "./run-tests",
            "--testlist=sparklib.txt",
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
    for entry in os.listdir(covtempdir):
        full_path = os.path.join(covtempdir, entry)
        if os.path.isdir(full_path):
            files = glob.glob(os.path.join(f"{full_path}/**", "*.sid"), recursive=True)
            if len(files) > 0:
                sidfiles = tempfile.NamedTemporaryFile(delete=False)
                for file in files:
                    sidfiles.write(file.encode("utf-8") + b"\n")
                sidfiles.close()
                return sidfiles
    print("didn't find any sid files")
    exit(1)


def produce_report(covlibdir, covtempdir):
    shutil.rmtree(covlibdir)
    trf = tracefiles(covtempdir)
    sid = sidfiles(covtempdir)
    try:
        os.environ["SPARKLIB_INSTALLED"] = "False"
        args = [
            "gnatcov",
            "coverage",
            "--annotate=dhtml",
            "--level=stmt",
            "--output-dir=sparklib-report",
            "--sid",
            f"@{sid.name}",
            "-P",
            "../../include/sparklib_internal.gpr",
            f"@{trf.name}",
        ]
        subprocess.run(args)
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
