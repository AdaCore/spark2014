#!/usr/bin/env python3
"""Apply the repository's project formatting to Ada files in the current edit."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
GNAT_SRC = (ROOT / "gnat2why/gnat_src").resolve()
PATCH_PATH = re.compile(r"^\*\*\* (?:Add File|Update File|Move to): (.+)$", re.M)


def edited_files(payload: dict) -> set[Path]:
    tool_input = payload.get("tool_input", {})
    paths = PATCH_PATH.findall(tool_input.get("command", ""))
    if "file_path" in tool_input:
        paths.append(tool_input["file_path"])

    cwd = Path(payload.get("cwd") or ROOT)
    result = set()
    for name in paths:
        path = (cwd / name).resolve()
        if (
            path.suffix in {".ads", ".adb"}
            and path.is_relative_to(ROOT)
            and not path.is_relative_to(GNAT_SRC)
            and path.is_file()
        ):
            result.add(path)
    return result


def project_files(project: str, edited: set[Path]) -> set[Path]:
    # Source_Dirs depends on the target and GPR_TOOL. Only inspect the closure
    # if the edit touched one of the root project's source directories.
    info = subprocess.check_output(
        ["gprinspect", "-P", project, "--display=json-compact"], cwd=ROOT
    )
    project_info = json.loads(info)["projects"][0]["project"]
    source_dirs = set(map(Path, project_info["source-directories"]))
    candidates = {path for path in edited if path.parent in source_dirs}
    if not candidates:
        return set()

    sources = subprocess.check_output(
        ["gprls", "-P", project, "-s", "--closure", "--source-parser"],
        cwd=ROOT,
        text=True,
    )
    return candidates.intersection(map(Path, sources.splitlines()))


def format_files(project: str, files: set[Path]) -> None:
    if files:
        subprocess.run(
            ["gnatformat", "-P", project, "--no-subprojects", *sorted(files)],
            cwd=ROOT,
            check=True,
        )


def main() -> None:
    edited = edited_files(json.load(sys.stdin))
    if not edited:
        return

    # Use the same project order and explicit table generator source as
    # "make format". A source shared by two projects goes through both.
    for project in ("gnatprove.gpr", "gnat2why/gnat2why.gpr"):
        format_files(project, project_files(project, edited))

    table_project = "docs/ug/table_generator/table_generator.gpr"
    table_source = (ROOT / table_project).with_suffix(".adb")
    format_files(table_project, edited.intersection({table_source}))


if __name__ == "__main__":
    main()
