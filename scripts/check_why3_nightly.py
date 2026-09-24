#!/usr/bin/env python3

"""
Decides whether the CI must build why3 from sources instead of using the
nightly build.

When a spark2014 change requires a matching why3 change and both are merged,
the CI keeps using the why3 of the last nightly build, which does not contain
the why3 change, until the next nightly. This script detects that situation:
it compares the why3 commit packaged by the nightly build with the current tip
of the corresponding why3 branch, and asks for a source build when they differ.

The comparison needs no clone: the nightly commit comes from a Cathod query,
and the branch tip from a single "git ls-remote" against the why3 repository.

The setup (and therefore the why3 branch) is derived from the target branch of
the merge request, mirroring the inference done by generic_anod_ci: a release
branch selects the setup of that release, anything else selects "wave". The
why3 branch itself is not hardcoded; it is read from the revision metadata that
Cathod records alongside the source package.

Output is meant to be spliced into the generic_anod_ci command line:

    OPTIONS="$OPTIONS $(python scripts/check_why3_nightly.py)"

so the script prints "--add-dep <why3 project>" on stdout when a source build
is needed, and nothing otherwise. All diagnostics go to stderr.

Nothing about the GitLab instance or the why3 repository is hardcoded. The
instance comes from the environment that GitLab provides to every job, and the
why3 repository from the submodule declaration of this very checkout, so a
move of either is followed automatically.

Authentication uses the job token, which is enough because this is a plain
repository read: the GitLab REST API is deliberately not used, as a job token
may not query project or branch metadata there.

The script fails open: if the nightly commit or the branch tip cannot be
determined, it prints a warning and no option, leaving the CI with the nightly
why3. This keeps a transient Cathod or GitLab outage from silently turning
every pipeline into a full why3 build. Pass --strict to fail closed instead,
requesting the source build whenever the check cannot conclude.

The exit status is always 0. The caller splices the output into a shell
assignment, where a non-zero status would abort the job under "set -e", so a
failure of the check must not be reported that way. The outcome is carried by
the output alone, and the reason for a fallback by the diagnostics.
"""

from __future__ import annotations

import argparse
import json
import os
import posixpath
import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import urlsplit, urlunsplit

from e3.cathod import CathodReadOnly

# Name of the why3 source package in Cathod.
SOURCE_PACKAGE = "why3-src"

# Name of the why3 submodule in this repository. The submodule declaration is
# what ties spark2014 to a why3 repository, so it is also the right place to
# learn which repository to query.
WHY3_SUBMODULE = "why3"

# User name that goes with a job token in a repository URL. It is fixed by
# GitLab and carries no secret.
JOB_TOKEN_USER = "gitlab-ci-token"

# How long to wait for the remote, in seconds. The query lists a single
# reference, so a short timeout is enough; an unresponsive service must not
# hold the whole pipeline back, and the check fails open anyway. Cathod applies
# its own default timeout.
QUERY_TIMEOUT = 30

# Branch names that map to the "wave" setup rather than to a release setup.
# This mirrors the inference performed by generic_anod_ci.
MAINLINE_BRANCHES = ("main", "master", "edge", "wavefront")

# A release branch, optionally under "releases/", possibly with a suffix.
RELEASE_BRANCH_RE = re.compile(
    r"(releases/)?(?P<release>([1-9][0-9]|gnat-7\.[1-4])(\.\d+|-sustained)).*"
)


def scrub(text: str) -> str:
    """Remove the job token from a message before it reaches the job log."""
    token = os.environ.get("CI_JOB_TOKEN")
    return text.replace(token, "***") if token else text


def warn(message: str) -> None:
    """Report a diagnostic on stderr."""
    print(f"check_why3_nightly: {scrub(message)}", file=sys.stderr)


def infer_setup() -> str:
    """Return the anod setup matching the merge request's target branch.

    Scheduled and non-merge-request pipelines have no target branch; they use
    the default setup, as generic_anod_ci does.
    """
    branch = os.environ.get("CI_MERGE_REQUEST_TARGET_BRANCH_NAME", "")
    if not branch:
        return "wave"

    match = RELEASE_BRANCH_RE.fullmatch(branch)
    if match:
        return match.group("release")

    if branch not in MAINLINE_BRANCHES:
        warn(f"unknown target branch {branch}, assuming the wave setup")
    return "wave"


def nightly_why3_revision(setup: str) -> dict[str, str]:
    """Return the revision metadata of why3 in the latest nightly build.

    The returned dictionary holds at least the branch and the commit that the
    nightly build packaged.
    """
    with CathodReadOnly() as cathod:
        files = cathod.get_latest_file_info(
            kind="source", setup=setup, name=SOURCE_PACKAGE
        )

    if not files:
        raise ValueError(f"no {SOURCE_PACKAGE} in the latest {setup} build")

    # The revision is stored as a JSON string mapping each repository of the
    # source package to its checkout information. why3 packages a single
    # repository.
    revisions = json.loads(files[0]["revision"])
    return next(iter(revisions.values()))


def why3_project_path() -> str:
    """Return the project path of why3 on the GitLab instance.

    The submodule declaration of this checkout is what ties spark2014 to a
    why3 repository, so it is also what tells where why3 lives. Git resolves a
    relative submodule URL against the location of the superproject, component
    by component; applying the same resolution to the project path of the
    superproject yields the project path of the submodule.
    """
    gitmodules = Path(__file__).resolve().parent.parent / ".gitmodules"
    url = subprocess.run(
        [
            "git",
            "config",
            "--file",
            str(gitmodules),
            "--get",
            f"submodule.{WHY3_SUBMODULE}.url",
        ],
        capture_output=True,
        text=True,
        check=True,
        timeout=QUERY_TIMEOUT,
    ).stdout.strip()

    if url.startswith(("./", "../")):
        path = posixpath.join(os.environ["CI_PROJECT_PATH"], url)
    else:
        path = urlsplit(url).path

    return posixpath.normpath(path).strip("/").removesuffix(".git")


def why3_repository_url(project_path: str) -> str:
    """Return the URL to read the why3 repository from.

    The job token is enough to read a repository, and reading a repository is
    all this check needs. It is embedded in the URL, which is therefore never
    reported as is.
    """
    server = urlsplit(os.environ["CI_SERVER_URL"])
    netloc = f"{JOB_TOKEN_USER}:{os.environ['CI_JOB_TOKEN']}@{server.netloc}"
    path = "/" + posixpath.join(server.path.strip("/"), f"{project_path}.git")
    return urlunsplit((server.scheme, netloc, path, "", ""))


def branch_tip(url: str, branch: str) -> str:
    """Return the commit at the tip of a branch of a remote repository."""
    result = subprocess.run(
        ["git", "ls-remote", "--exit-code", url, f"refs/heads/{branch}"],
        capture_output=True,
        text=True,
        timeout=QUERY_TIMEOUT,
        # Credentials that the job token does not cover must make the query
        # fail rather than wait for an answer that no one is there to give.
        env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
    )
    if result.returncode != 0:
        # An absent branch is reported by the exit status alone, with nothing
        # on stderr, so it needs a message of its own.
        reason = result.stderr.strip() or "no such branch"
        raise ValueError(f"cannot read branch {branch}: {reason}")

    return result.stdout.split()[0]


def request_source_build(project_path: str) -> None:
    """Print the option asking generic_anod_ci to build why3 from sources.

    The option designates the repository by its path, which is how
    generic_anod_ci looks it up in the sandbox configuration.
    """
    print(f"--add-dep {project_path}")


def main() -> int:
    """Print the generic_anod_ci option needed to get an up to date why3."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--strict",
        action="store_true",
        help="request a source build when the check cannot conclude",
    )
    args = parser.parse_args()

    setup = infer_setup()

    # The project is resolved first, as the fallback below needs its path too.
    project_path = None

    try:
        project_path = why3_project_path()
        revision = nightly_why3_revision(setup)
        branch = revision["revision"]
        nightly_commit = revision["new_commit"]
        tip = branch_tip(why3_repository_url(project_path), branch)
    # Any failure of the probe is a reason to fall back, not a reason to break
    # the pipeline: the exception types the two services can raise are neither
    # documented nor stable, and an uncaught one would abort the CI setup.
    except Exception as e:  # noqa: BLE001
        warn(f"cannot compare why3 with the nightly build: {e}")
        if args.strict and project_path is not None:
            warn("strict mode: requesting a source build of why3")
            request_source_build(project_path)
            return 0
        if args.strict:
            warn("strict mode: but the why3 repository could not be located")
        warn("keeping the nightly why3")
        return 0

    warn(f"setup {setup}, why3 branch {branch}")
    warn(f"nightly why3: {nightly_commit}")
    warn(f"{project_path} tip: {tip}")

    if nightly_commit == tip:
        warn("the nightly why3 is up to date")
        return 0

    warn("why3 moved since the nightly build, building it from sources")
    request_source_build(project_path)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:  # noqa: BLE001
        # The caller splices our output into a shell assignment under "set -e",
        # so exiting non-zero would abort the job. Report and fall back.
        warn(f"unexpected error: {e}")
        warn("keeping the nightly why3")
        sys.exit(0)
