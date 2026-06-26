#!/usr/bin/env python3

"""Report obsolete XFAIL/SKIP entries in the gnatprove testsuite.

A test is marked XFAIL (or SKIP) either through a legacy ``test.opt`` file or
through a rule in the central ``mass_xfail.yaml`` file. In both cases an
associated GitLab issue (TN) justifies the entry. Once that issue is closed
(or no longer exists), the entry is obsolete and the test should be re-enabled.

This script scans both mechanisms and prints, for every entry, the cases where
no associated issue is still open. Entries whose associated issues are all in
the "Won't do" status are skipped: the test is expected to stay disabled, so
there is nothing to act on.

Run from ``testsuite/gnatprove/`` (or pass ``--root``).
"""

import argparse
import glob
import os
import re
import sys

import gitlab
import gitlab.exceptions
import yaml

# Make the shared testsuite utilities importable when running from scripts/.
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from lib.python.gitlab_util import (  # noqa: E402
    SPARK2014_GITLAB_ID,
    issue_status_name,
    make_gitlab_client,
)

# Work item Status of an issue that was deliberately closed as not-to-be-fixed.
WONT_DO = "Won't do"

# Reference to a GitLab issue, e.g. "eng/spark/spark2014#1377".
issue_re = re.compile(r"[A-Za-z0-9\-/]+#[0-9]+")
# Leading number in a test name, used as a spark2014 issue number by convention.
numre = re.compile(r"[0-9]+")
# test.opt directives that disable a test, fully or partially.
disable_re = re.compile(r"\b(?:XFAIL|SKIP)\b")

SPARK2014 = "eng/spark/spark2014"

# Subdirectories (relative to the testsuite root) that hold tests with a
# legacy test.opt file.
LEGACY_TEST_DIRS = ["tests", "internal", "sparklib"]


def get_issue(gl, cache, issue_ref):
    """Return the GitLab issue for a reference like ``group/proj#123``.

    Results are memoized in ``cache`` since many entries share the same issue.
    Return None if the issue cannot be resolved.
    """
    if issue_ref in cache:
        return cache[issue_ref]
    issue = None
    try:
        project_name, issue_id = issue_ref.split("#")
        if project_name == SPARK2014:
            project = gl.projects.get(SPARK2014_GITLAB_ID, lazy=True)
        else:
            project = gl.projects.get(project_name)
        issue = project.issues.get(issue_id)
    except (ValueError, gitlab.exceptions.GitlabError):
        issue = None
    cache[issue_ref] = issue
    return issue


def has_open_issue(gl, cache, issue_refs):
    """Return True if at least one of the referenced issues is still open."""
    for ref in issue_refs:
        issue = get_issue(gl, cache, ref)
        if issue is not None and issue.state == "opened":
            return True
    return False


def assignee_of(gl, cache, issue_refs):
    """Return a printable assignee for the first resolvable issue, or ""."""
    for ref in issue_refs:
        issue = get_issue(gl, cache, ref)
        if issue is None:
            continue
        assignee = getattr(issue, "assignee", None)
        if isinstance(assignee, dict):
            return assignee.get("name") or assignee.get("username") or ""
        if assignee:
            return str(assignee)
        return ""
    return ""


def all_wont_do(gl, status_cache, issue_refs):
    """Return True if every referenced issue resolves to the "Won't do" status.

    Such entries are deliberately kept disabled, so they are not reported as
    obsolete. Results are memoized in ``status_cache``. Return False as soon as
    a reference has a resolvable status other than "Won't do".

    A status lookup can fail transiently. Since "Won't do" is rare, a failed
    lookup most likely hides a genuinely done issue, so we default to "Done"
    (and thus report the entry) rather than silently keep a possibly obsolete
    test disabled. A warning on stderr flags that the status was assumed.
    """
    if not issue_refs:
        return False
    for ref in issue_refs:
        try:
            project_path, iid = ref.split("#")
        except ValueError:
            return False
        if ref not in status_cache:
            try:
                status_cache[ref] = issue_status_name(gl, project_path, iid)
            except RuntimeError:
                print(
                    f"warning: failed to retrieve status of {ref}; "
                    f"assuming status is Done",
                    file=sys.stderr,
                )
                status_cache[ref] = "Done"
        if status_cache[ref] != WONT_DO:
            return False
    return True


def test_disabled_kinds(testdir):
    """Return how the test in ``testdir`` is disabled, and its justifying issues.

    A ``test.opt`` file disables a test (fully or partially) through an
    ``XFAIL`` or ``SKIP`` directive; in both cases an associated issue is
    expected to justify the entry. Return a ``(kinds, refs)`` pair where
    ``kinds`` is the set of directives found (e.g. ``{"SKIP"}``) and ``refs``
    the referenced issues. Return None if the test is not disabled through
    ``test.opt``.

    Issues explicitly mentioned in ``test.opt`` are used as-is. The leading
    number of the test name is used as a spark2014 issue only when no explicit
    reference is present: inferring it unconditionally would let an unrelated
    (and possibly open) issue mask a wrong or obsolete explicit reference.
    """
    test_opt = os.path.join(testdir, "test.opt")
    if not os.path.exists(test_opt):
        return None
    with open(test_opt, "rb") as f:
        text = f.read().decode("utf-8")
    kinds = set(re.findall(disable_re, text))
    if not kinds:
        return None
    refs = re.findall(issue_re, text)
    if not refs:
        testname = os.path.basename(testdir)
        m = re.match(numre, testname)
        if m:
            refs = [f"{SPARK2014}#{m.group(0)}"]
    return kinds, refs


def check_legacy_tests(gl, cache, status_cache, root):
    """Report disabled tests (via test.opt) whose issues are all closed/missing."""
    tests = []
    for subdir in LEGACY_TEST_DIRS:
        tests += glob.glob(os.path.join(root, subdir, "*"))
    for test in sorted(tests):
        if not os.path.isdir(test):
            continue
        testname = os.path.basename(test)
        disabled = test_disabled_kinds(test)
        if disabled is None:
            continue
        kinds, refs = disabled
        kind = "/".join(sorted(kinds))
        if not refs:
            print(f"test {testname} is {kind}, but there is no TN")
            continue
        if not has_open_issue(gl, cache, refs):
            if all_wont_do(gl, status_cache, refs):
                continue
            assignee = assignee_of(gl, cache, refs)
            print(
                f"test {testname} is {kind}, but none of its associated issues "
                f"{refs} are open ({assignee})"
            )


def check_mass_xfail(gl, cache, status_cache, root):
    """Report mass_xfail.yaml rules whose associated issue is closed/missing."""
    mass_file = os.path.join(root, "mass_xfail.yaml")
    if not os.path.exists(mass_file):
        return
    with open(mass_file, "r") as f:
        data = yaml.safe_load(f) or {}
    for rule in data.get("rules", []):
        action = rule.get("action", "xfail")
        issue_ref = rule.get("issue")
        refs = [issue_ref] if issue_ref else []
        rule_tests = rule.get("tests", [])
        if not refs:
            print(
                f"mass_xfail rule {action!r} for {len(rule_tests)} test(s) "
                f"has no TN: {rule.get('description', '')}"
            )
            continue
        if not has_open_issue(gl, cache, refs):
            if all_wont_do(gl, status_cache, refs):
                continue
            assignee = assignee_of(gl, cache, refs)
            print(
                f"mass_xfail rule {action!r} ({issue_ref}) is obsolete: "
                f"the issue is not open ({assignee}); affects "
                f"{len(rule_tests)} test(s): {', '.join(rule_tests)}"
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default=".",
        help="Path to the testsuite/gnatprove directory (default: .)",
    )
    parser.add_argument(
        "--no-legacy",
        action="store_true",
        help="Skip the legacy test.opt scan",
    )
    parser.add_argument(
        "--no-mass",
        action="store_true",
        help="Skip the mass_xfail.yaml scan",
    )
    args = parser.parse_args()

    gl = make_gitlab_client()
    cache = {}
    status_cache = {}
    if not args.no_mass:
        check_mass_xfail(gl, cache, status_cache, args.root)
    if not args.no_legacy:
        check_legacy_tests(gl, cache, status_cache, args.root)


if __name__ == "__main__":
    main()
