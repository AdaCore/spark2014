#!/usr/bin/env python3

"""
Checks that a commit message references an issue via an "Issue:" trailer.

Intended to be used as a pre-commit hook running at the "commit-msg" stage.
The path to the file holding the commit message is passed as the sole
positional argument (the convention pre-commit uses for commit-msg hooks).

The trailer value must be a GitLab issue reference in "#NNN" form, optionally
prefixed by a project path, for example:

    Issue: eng/spark/spark2014#1406          (full path, any project)
    Issue: #1406                             (short form, this project)

References to issues in any project are accepted, not only this one. The check
is robust to surrounding whitespace and to the case of the "Issue" label, but a
bare number or free text is rejected: the value must be a recognizable issue
reference.

A commit that deliberately has no associated issue can opt out of the check by
including the string "no-issue-check" anywhere in its message.

Exit codes:
- 0: A well-formed "Issue:" trailer was found, or the check was bypassed.
- 1: No well-formed "Issue:" trailer was found.
- 2: An unexpected error occurred (e.g. the message file is missing).
"""

import argparse
import re
import sys

# A GitLab issue reference: "#NNN", optionally prefixed by a project path
# (e.g. "eng/spark/spark2014#NNN").
ISSUE_REF = r"[\w./-]*#[0-9]+"

# Trailer form, tolerant of whitespace around the label and value and of the
# case of the "Issue" label. Comment lines (starting with '#') do not match
# because the label must be at the start of the line.
ISSUE_TRAILER = re.compile(
    r"^[ \t]*Issue:[ \t]*" + ISSUE_REF + r"[ \t]*$",
    re.IGNORECASE | re.MULTILINE,
)

EXAMPLE = "Issue: eng/spark/spark2014#1406"

# Marker that lets a commit opt out of the issue-trailer requirement.
BYPASS = "no-issue-check"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "commit_msg_file",
        help="Path to the file containing the commit message.",
    )
    args = parser.parse_args()

    try:
        with open(args.commit_msg_file, encoding="utf-8") as f:
            message = f.read()
    except OSError as e:
        print(f"error: cannot read commit message file: {e}", file=sys.stderr)
        return 2

    if BYPASS in message.lower():
        return 0

    if ISSUE_TRAILER.search(message):
        return 0

    print(
        "error: commit message is missing a well-formed 'Issue:' trailer.\n"
        f"       Add a line of the form: {EXAMPLE}\n"
        f"       or include {BYPASS!r} in the message to bypass this check.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
