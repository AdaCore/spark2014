#!/usr/bin/env python3
"""Format changed Ada files after Codex edits."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


ADA_RE = re.compile(r'[^\s"\'<>]+\.(?:ads|adb)')


def walk_strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for item in value.values():
            yield from walk_strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from walk_strings(item)


def collect_paths(payload: dict[str, Any]) -> list[str]:
    paths: list[str] = []
    for text in walk_strings(payload):
        paths.extend(ADA_RE.findall(text))
    return paths


def git_changed_paths(repo_root: Path) -> list[str]:
    try:
        result = subprocess.run(
            [
                "git",
                "diff",
                "--name-only",
                "--diff-filter=ACMRTUXB",
                "HEAD",
            ],
            cwd=repo_root,
            check=True,
            text=True,
            capture_output=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return []

    paths: list[str] = []
    for line in result.stdout.splitlines():
        if line.endswith((".ads", ".adb")):
            paths.append(line)

    try:
        status = subprocess.run(
            [
                "git",
                "status",
                "--porcelain=v1",
                "--untracked-files=all",
            ],
            cwd=repo_root,
            check=True,
            text=True,
            capture_output=True,
        )
    except (OSError, subprocess.CalledProcessError):
        status = None

    if status is not None:
        for line in status.stdout.splitlines():
            if len(line) >= 4:
                candidate = line[3:]
                if candidate.endswith((".ads", ".adb")):
                    paths.append(candidate)

    return paths


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except json.JSONDecodeError:
        return 0

    repo_root = Path(payload.get("cwd") or os.getcwd())
    paths = collect_paths(payload)
    if not paths:
        paths = git_changed_paths(repo_root)

    unique_paths = []
    for raw_path in paths:
        candidate = Path(raw_path)
        if not candidate.is_absolute():
            candidate = repo_root / candidate
        try:
            candidate = candidate.resolve()
        except OSError:
            continue
        if candidate.exists() and candidate.suffix in {".ads", ".adb"}:
            try:
                unique_paths.append(str(candidate.relative_to(repo_root)))
            except ValueError:
                continue

    unique_paths = sorted(set(unique_paths))
    if not unique_paths:
        return 0

    try:
        subprocess.run(["gnatformat", *unique_paths], cwd=repo_root, check=False)
    except OSError:
        return 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
