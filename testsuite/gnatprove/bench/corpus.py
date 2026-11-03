#!/usr/bin/env python3
"""Create, verify and package an inventory of benchmark prover inputs."""

import argparse
import datetime
import hashlib
import json
import shutil
from pathlib import Path
import subprocess
import sys
import tarfile

MANIFEST = "corpus-manifest.json"


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def revision(directory):
    try:
        root = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "--show-toplevel"],
            stderr=subprocess.DEVNULL,
            text=True,
        ).strip()
        if Path(root).resolve() != Path(directory).resolve():
            print(
                f"warning: cannot record revision for {directory}: "
                f"Git root is {root}",
                file=sys.stderr,
            )
            return None
        rev = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"],
            stderr=subprocess.DEVNULL,
            text=True,
        ).strip()
        dirty = subprocess.check_output(
            [
                "git",
                "-C",
                str(directory),
                "status",
                "--porcelain",
                "--untracked-files=no",
            ],
            stderr=subprocess.DEVNULL,
            text=True,
        )
        return {"root": root, "commit": rev, "tracked_changes": bool(dirty)}
    except (OSError, subprocess.CalledProcessError) as exc:
        print(
            f"warning: cannot record revision for {directory}: {exc}", file=sys.stderr
        )
        return None


def inventory(root):
    result = []
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"symlink in corpus: {path}")
        if path.is_file() and path.suffix in (".smt2", ".psmt2"):
            rel = path.relative_to(root)
            if len(rel.parts) != 3:
                raise ValueError(f"unexpected VC path: {rel}")
            result.append(
                {
                    "path": rel.as_posix(),
                    "size": path.stat().st_size,
                    "sha256": digest(path),
                }
            )
    return result


def tool_version(name):
    executable = shutil.which(name)
    if executable is None:
        return None
    try:
        output = subprocess.check_output(
            [executable, "--version"], stderr=subprocess.STDOUT, text=True, timeout=10
        ).strip()
    except (OSError, subprocess.SubprocessError):
        output = None
    return {"executable": executable, "version": output}


def write_manifest(resultdir, testsuitedir, testlist, runs):
    root = Path(resultdir)
    suite = Path(testsuitedir).resolve()
    repo = suite.parent.parent
    selection = None
    if testlist:
        selection = {
            "path": str(Path(testlist).resolve()),
            "sha256": digest(Path(testlist)),
            "content": Path(testlist).read_text(),
        }
    manifest = {
        "schema_version": 1,
        "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "source": revision(repo),
        "why3": revision(repo / "why3"),
        "gnatprove": tool_version("gnatprove"),
        "test_selection": selection,
        "generation": {"discriminants": ["large"], "runs": runs},
        "files": inventory(root),
    }
    (root / MANIFEST).write_text(json.dumps(manifest, indent=2) + "\n")


def verify(root):
    manifest = json.loads((root / MANIFEST).read_text())
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported corpus manifest version")
    actual = inventory(root)
    if not actual or actual != manifest.get("files"):
        raise ValueError("corpus inventory differs from manifest")
    counts = {r["prover"]: r["vc_count"] for r in manifest["generation"]["runs"]}
    actual_counts = {
        p: sum(f["path"].split("/")[1] == p for f in actual) for p in counts
    }
    if counts != actual_counts or sum(counts.values()) != len(actual):
        raise ValueError("prover counts differ from manifest")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    check = sub.add_parser("verify")
    check.add_argument("directory", type=Path)
    pack = sub.add_parser("pack")
    pack.add_argument("directory", type=Path)
    pack.add_argument("archive", type=Path)
    args = parser.parse_args()
    root = args.directory.resolve()
    manifest = verify(root)
    if args.action == "pack":
        archive = args.archive.resolve()
        if archive.is_relative_to(root):
            parser.error("archive must be outside the corpus directory")
        with tarfile.open(archive, "x:gz") as tar:
            tar.add(root / MANIFEST, arcname=MANIFEST, recursive=False)
            for item in manifest["files"]:
                tar.add(root / item["path"], arcname=item["path"], recursive=False)
        print(f"Wrote {archive}")
    print(f"Verified {len(manifest['files'])} files in {root}")


if __name__ == "__main__":
    main()
